
// Boolean type is defined
// open util/boolean


//********************  Signatures for the overall system *************************//
// All the signatures are defined based on class diagram 
// For the timestamps and duration operations, addition/subtraction and all types of comparisons
// are needed. Therefore, "Natural" type is employed for this purpose in this alloy model. 
open util/natural
open util/integer
// Since an order is needed for user preference list of mobility options, Priority signature is used
// with ordering utilization
open util/ordering[Priority] as po
// Necessary Data structures for string 
sig Str{} 

// Signature for events
sig Event{
	location: one Str,
	StartTime: one Natural,
	EndTime: one Natural,
	ChosenMobility: one Mobility,
	periodicity : one PeriodicityStatus,
	name: one Str
}{
one StartTime
one EndTime
// Start time is always before end time
lt[StartTime , EndTime]
}
abstract sig PeriodicityStatus{ }
lone sig OneTime,Daily,Weekly,Monthly extends PeriodicityStatus{ }

// Extension for customized events
sig CustomizedEvent extends Event {
	Duration: one Natural
}
{
	one Duration
	// Duration for customized event is always greater than zero and less than or equal to time between start and endtime
	gt[ Duration,Zero]
    lte[Duration , sub[sub[EndTime,StartTime],ChosenMobility.TravelDuration] ]
}

// Signatures for related Mobility Options

abstract sig mobilityStatus {}
one sig Activated extends mobilityStatus{}
one sig Deactivated extends mobilityStatus{}
one sig Car,Tram,Train,Metro,Bus,Bike,Walk extends Mobility{}
sig Priority{}

abstract sig Mobility{
	// No mobility can be used in between restrictedStartTime and restrictedEndTime  
	restrictedStartTime: one Natural,
	restrictedEndTime: one Natural,
	status: one mobilityStatus,	
	// Maximum allowed duration by user 
	durationLimit: lone Natural,
	TravelDuration: one Natural,

}
{
	gt[restrictedEndTime,restrictedStartTime]
}

// Signature for Calendar
sig Calendar {
	EventList: some Event,
	MobilityList = EventList.ChosenMobility
}

// Signature for User
sig User {
	username: one Str,
	password: one Str,
	calendar: one Calendar,
	mlist: one PreferenceList
}
{
// One username,password and calendar for each users
	one username
	one password
	one calendar
	one mlist
}

// Signatures for related PreferenceList
sig PreferenceList {
	listName : one Str,
	MobilityList: set Mobility,
	priorityList:set Priority,
	mplist : ( MobilityList -> one Priority )
}{
	#priorityList > 0
	#MobilityList > 0
	#priorityList = # MobilityList
	no disjoint m1,m2: MobilityList | mplist[m1] =mplist[m2]
}
// Default is predefined lists that are focused on particular subjects such as footprint minimization, cost minimization etc.
sig Default extends PreferenceList {}
sig CustomizedList extends PreferenceList {}

// *********************  Facts start here *********************** //
fact uniqueUsername {
	no disjoint u1,u2:  User | u1.username = u2.username
}

fact uniquePreferenceList {
	no disjoint u1,u2:  User | u1.mlist = u2.mlist
}
fact uniqueCalender {
	no disjoint u1,u2:  User | u1.calendar = u2.calendar
}
fact uniqueEvents {
	no disjoint c1,c2: Calendar,e:Event | e in c1.EventList and e in c2.EventList
}
// one calendar and preference list for each user
// No unowned calendar or preference list occur
fact Cardinality {

	 #Calendar = #User 
	 #PreferenceList = #User
     #Event=#PeriodicityStatus
}

// Choose top mobility option in user preferences
fact chooseTopMobilityOption {
	all  u:User ,
		  m : u.calendar.EventList.ChosenMobility|
		  m = ((u.mlist).mplist).(min[u.mlist.priorityList]) 
}
fact NoDeactiveMobilityOptionInPreferenceList {
	no u:User, m:Mobility | m.status=Deactivated and m in u.mlist.MobilityList
}
// No overlapping event occur 
fact noOverlappingEventInCalendar {
	// If the events are not customized, then start time of any event cannot be between start time and end time of any other event
 	no disjoint e, e2 : Calendar.EventList  | e != CustomizedEvent and e2 != CustomizedEvent and
																	gte[e.StartTime, sub[e2.StartTime,e2.ChosenMobility.TravelDuration]] and 
																 	lte[sub[e.StartTime,e.ChosenMobility.TravelDuration] ,e2.EndTime]
	// If the events are customized, there should be enough time for customized event duration between two events
	no disjoint e1,e2,ce : Calendar.EventList |  e1 != CustomizedEvent and e2 != CustomizedEvent and
																		 ce = CustomizedEvent and gt[e1.StartTime , e2.EndTime] and
																		 lte[ce.StartTime, e2.EndTime] and gte[ce.EndTime , e2.EndTime] and
																		 gt[add[ce.Duration,ce.ChosenMobility.TravelDuration] , sub[sub[e1.StartTime,e1.ChosenMobility.TravelDuration],  e2.EndTime] ]
	
	no disjoint e1,ce: Calendar.EventList | (e1 != CustomizedEvent and ce = CustomizedEvent) and
																  (lt[e1.StartTime,ce.StartTime] and gt[add[add[sub[e1.EndTime,e1.StartTime],ce.Duration],ce.ChosenMobility.TravelDuration], sub[ce.EndTime,e1.StartTime]]) or
																  (lt[ce.StartTime,e1.StartTime] and gt[add[add[sub[e1.EndTime,e1.StartTime],ce.Duration],e1.ChosenMobility.TravelDuration], sub[e1.EndTime,ce.StartTime]])
	no disjoint ce1,ce2: Calendar.EventList | (ce1 = CustomizedEvent and ce2 = CustomizedEvent) and
																  (lt[ce1.StartTime,ce2.StartTime] and gt[add[add[ce1.Duration,ce2.Duration],ce2.ChosenMobility.TravelDuration], sub[ce2.EndTime,ce1.StartTime]]) 
																  


}																  


--CHOOSING MOBILITY
--deactivated Mobility cannot be on the PreferenceList
fact onlyActiveMobilitiesOnTheList{ all m:Mobility,p:PreferenceList| m in p.MobilityList <=> m.status=Activated }
 
--Mobility that is not on Preference List cannot be chosen
fact ChosenMobilityMustBeOnPreferenceList{all e:Event,p:PreferenceList|e.ChosenMobility in p.MobilityList}

fact NoTravelDurationIfMobilityIsNotChosen{all m:Mobility, e:Event| lt[m.TravelDuration, Zero] => m!=e.ChosenMobility}

fact DeactivatedIfTravelInRestrictedTime {
	all u:User,e : u.calendar.EventList , m:u.mlist.MobilityList | (gte[m.restrictedStartTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedStartTime ,e.StartTime] ) or gte[m.restrictedEndTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedEndTime ,e.StartTime] implies m.status = Deactivated
}

// If Travel duration is more than duration limit, the mobility is deactivated
// For instance, if it lasts 1 hour to walk somewhere then,
// however the limit for walking is 30 minutes
// walk option is deactivated
fact DeactivatedIfTravelDurationIsMoreThanLimit 
{
	all m:Mobility | gt[m.TravelDuration, m.durationLimit] => m.status = Deactivated
}
pred RegisterNewUser[u,up,unew:User] {
	up = u + unew
}
pred editEvent [c,cp:Calendar,e :c.EventList, 
		nStartTime: Natural,
		nEndTime: Natural] {
	
// Edit an event by deleting previous event and adding altered one	
	all ep:Event | ep.StartTime = nStartTime and	ep.EndTime = nEndTime
	and deleteEvent[c,cp,e] and addEvent[c,cp,ep] 
	
}

pred addEvent[c,c':Calendar, e:Event ] { 
	c'.EventList = c.EventList + e
}
pred deleteEvent[c,c':Calendar, e:Event ] {
	c'.EventList = c.EventList - e
}
pred showAddDelete[c,c':Calendar, e:Event ] {
	//
	#User = 1
	#Mobility = #PreferenceList.MobilityList
	#Event = 2
    //addEvent[c,c',e]
	//deleteEvent[c,c',e]
	
}
assert RegisterUser{
	all u,up,unew:User | unew not in u and RegisterNewUser[u,up,unew] implies unew.username not in u.username 
}

assert AddDeleteUndo {
	all c,c',c'' : Calendar, e : Event | e not in c.EventList and 
    addEvent[c,c',e] and deleteEvent[c',c'',e] 
	implies c.EventList = c''.EventList
}

assert AddTwoEventInSameTimeInterval{
// Same event cannot be added two times
	no e,ep: Event,u:User, c,c':u.calendar | ep=e and e not in c.EventList and addEvent[c,c',e] and  addEvent[c,c',ep]

}

assert EditEvent {
// Compare two calendar after edit on a event
	all u:User,cp,c: u.calendar, e:c.EventList ,nStartTime:Natural,
		nEndTime: Natural | editEvent [c,cp,e ,nStartTime,
		nEndTime	]  implies c != cp
}

--PREDICATES
--pred reachable
--pred IsCalendarFeasible

pred show{
// For Instance, due to weather , bike and walk is deactivated
Bike.status = Activated
Walk.status = Activated
#User =3 
}
run show for 7
check AddDeleteUndo
check EditEvent
check AddTwoEventInSameTimeInterval
check RegisterUser
