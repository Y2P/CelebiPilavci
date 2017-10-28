
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
	StartTime: one Int,
	EndTime: one Int,
	ChosenMobility: one Mobility,
	periodicity : one PeriodicityStatus,
	name: one Str
}{
one StartTime
StartTime > 0
one EndTime
EndTime  > 0
// Start time is always before end time
lt[StartTime , EndTime]
}
abstract sig PeriodicityStatus{ }
lone sig OneTime,Daily,Weekly,Monthly extends PeriodicityStatus{ }

// Extension for customized events
sig CustomizedEvent extends Event {
	Duration: one Int
}
{
	one Duration
	// Duration for customized event is always greater than zero and less than or equal to time between start and endtime
	gt[ Duration,0]
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
	restrictedStartTime: one Int,
	restrictedEndTime: one Int,
	status: one mobilityStatus,	
	// Maximum allowed duration by user 
	durationLimit: lone Int,
	TravelDuration: one Int,

}
{	
	restrictedStartTime > 0
	restrictedEndTime > 0
	durationLimit > 0
	TravelDuration > 0
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
	MobilityList: some Mobility,
	priorityList:some Priority,
	mplist : ( MobilityList -> one priorityList)
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
	all e, e2 : Calendar.EventList  | (e != e2  and e != CustomizedEvent and e2 != CustomizedEvent) implies
													   (e.StartTime != e2.StartTime or e.EndTime != e2.EndTime)

	all e, e2 : Calendar.EventList  | (e != CustomizedEvent and e2 != CustomizedEvent and
																	gt[e.StartTime, e2.StartTime] ) implies 
																 	gte[sub[e.StartTime,e.ChosenMobility.TravelDuration] ,e2.EndTime]
	// If one event is customized and others are not, there should be enough time for customized event duration between two events
	all e1,e2,ce : Calendar.EventList |(  e1 != CustomizedEvent and e2 != CustomizedEvent and
																		 ce = CustomizedEvent and gt[e1.StartTime , e2.EndTime] and
																		 lte[ce.StartTime, e1.EndTime] and gte[ce.EndTime , e2.EndTime] ) implies
																		 lte[add[ce.Duration,ce.ChosenMobility.TravelDuration] , sub[sub[e1.StartTime,e1.ChosenMobility.TravelDuration],  e2.EndTime] ]


// If there are one event and one customized event, total duration of both should be less than time between start time of previous one and end time of next one
	all e1,ce: Calendar.EventList |( (e1 != CustomizedEvent and ce = CustomizedEvent) and 
																  (lte[e1.StartTime,ce.StartTime] ) ) implies( gt[ce.EndTime,e1.EndTime]  and lte[add[add[sub[e1.EndTime,e1.StartTime],ce.Duration],ce.ChosenMobility.TravelDuration], sub[ce.EndTime,e1.StartTime]]) 
	all e1,ce: Calendar.EventList | ((e1 != CustomizedEvent and ce = CustomizedEvent) and 
																  (lt[ce.StartTime,e1.StartTime] )) implies lte[add[add[sub[e1.EndTime,e1.StartTime],ce.Duration],e1.ChosenMobility.TravelDuration], sub[e1.EndTime,ce.StartTime]] 


	// If there are two customized events, total duration of both,total duration of both should be less than time between start time of previous one and end time of next one 
	all ce1,ce2: Calendar.EventList |(ce1 != ce2 and (ce1 = CustomizedEvent and ce2 = CustomizedEvent) and
																  lte[ce1.StartTime,ce2.StartTime]) implies lt[add[add[ce1.Duration,ce2.Duration],ce2.ChosenMobility.TravelDuration], sub[ce2.EndTime,ce1.StartTime]]
																  

}																  


--CHOOSING MOBILITY
--deactivated Mobility cannot be on the PreferenceList
fact onlyActiveMobilitiesOnTheList{ all m:Mobility,p:PreferenceList| m in p.MobilityList <=> m.status=Activated }
 
--Mobility that is not on Preference List cannot be chosen
fact ChosenMobilityMustBeOnPreferenceList{all e:Event,p:PreferenceList|e.ChosenMobility in p.MobilityList}

fact NoTravelDurationIfMobilityIsNotChosen{all m:Mobility, e:Event| lt[m.TravelDuration, 0] => m!=e.ChosenMobility}

fact DeactivatedIfTravelInRestrictedTime {
	all u:User,e : u.calendar.EventList , m:u.mlist.MobilityList | (gte[m.restrictedStartTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedStartTime ,e.StartTime] ) or (gte[m.restrictedEndTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedEndTime ,e.StartTime]) <=> m.status = Deactivated
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
pred editEvent [c,cp:Calendar,e ,ep:Event] {

	deleteEvent[c,cp,e]
	addEvent[c,cp,ep]
// Edit an event by deleting previous event and adding altered one	

}

pred addEvent[c,c':Calendar, e:Event ] { 
	c'.EventList = c.EventList + e
}
pred deleteEvent[c,c':Calendar, e:Event ] {
	c'.EventList = c.EventList - e
}
pred showAddEvent[c,c':Calendar, e:Event ] {
	#User =1
	#User.calendar.EventList = 3
	#CustomizedEvent = 1
    addEvent[c,c',e]
	
}
pred showDeleteEvent[c,c':Calendar, e:Event ] {
	#User =1
	deleteEvent[c,c',e]
	
}
assert RegisterUser{
	all u,up,unew:User | unew not in u and RegisterNewUser[u,up,unew] implies unew.username not in u.username 
}

assert AddDeleteUndoEvent {
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
	all u:User,cp,c: u.calendar, e:c.EventList ,ep: Event| editEvent [c,cp,e ,ep]  implies c != cp
}
// Checks wheteher chosen mobility option by an event is the top of user preference list
assert MobilityOptionPriority {
	all u:User, m1:u.mlist.MobilityList,m2:u.calendar.EventList.ChosenMobility | lte[u.mlist.mplist[m2],u.mlist.mplist[m1]]
}
// Checks Mobility option is feasible various scenarios 
assert MobilityOptionFeasibility {
	all u:User, c:u.calendar ,e1 ,e2: c.EventList  |e1 != e2 and e1!=CustomizedEvent and e2!=CustomizedEvent and
											gt[e1.StartTime,e2.StartTime] implies gte[sub[e1.StartTime,e1.ChosenMobility.TravelDuration],e2.EndTime]

	all u:User, c:u.calendar ,e1 ,e2: c.EventList  |e1 != e2 and e1=CustomizedEvent and e2!=CustomizedEvent and
											gt[e1.StartTime,e2.StartTime] implies gte[sub[e1.EndTime,e2.StartTime] , add[add[sub[e2.EndTime,e2.StartTime],e1.Duration],e1.ChosenMobility.TravelDuration]]
	
	all u:User, c:u.calendar ,e1 ,e2: c.EventList  |e1 != e2 and e1=CustomizedEvent and e2=CustomizedEvent and
											gt[e1.StartTime,e2.StartTime] implies gte[sub[e1.EndTime,e2.StartTime] , add[add[e2.Duration,e1.Duration],e1.ChosenMobility.TravelDuration]]
	
}
--PREDICATES
--pred reachable
--pred IsCalendarFeasible

pred DeactivateMobilityOptions{
// For Instance, due to weather , bike and walk is deactivated
Bike.status = Deactivated
Walk.status = Deactivated
#User =1
#User.calendar.EventList = 3
#CustomizedEvent = 1
}
pred MultipleUsers {
	#User > 1
}


run DeactivateMobilityOptions for 7 Int
run showAddEvent for 7
run showDeleteEvent for 7
run editEvent for 7 Int
run MultipleUsers for 7 

check AddDeleteUndoEvent
check EditEvent
check AddTwoEventInSameTimeInterval
check RegisterUser
check MobilityOptionPriority for 7 Int
check MobilityOptionFeasibility for 7 Int
