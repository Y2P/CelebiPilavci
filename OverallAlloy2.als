
// Boolean type is defined
// open util/boolean


//********************  Signatures for the overall system *************************//
// All the signatures are defined based on class diagram 

open util/natural
open util/integer
// Necessary Data structures for string and datetime 
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
	gt[ Duration,Zero]
//	lte[Duration , sub[sub[EndTime,StartTime],ChosenMobility.TravelDuration] ]
}

// Signatures for related Mobility Options

abstract sig mobilityStatus {}
one sig Activated extends mobilityStatus{}
one sig Deactivated extends mobilityStatus{}
one sig Car,Tram,Train,Metro,Bus,Bike,Walk extends Mobility{}

abstract sig Mobility{
	restrictedStartTime: one Natural,
	restrictedEndTime: one Natural,
	status: one mobilityStatus,	
	durationLimit: lone Natural,
	TravelDuration: one Natural,
	Priority: Int
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
	MobilityList: some Mobility
}

sig Default extends PreferenceList {
	listName : one Str
}
sig CustomizedList extends PreferenceList {}

// *********************  Facts start here *********************** //
fact uniqueUsername {
	no disjoint u1,u2:  User | u1.username = u2.username
}

fact uniqueCalender {
	no disjoint u1,u2:  User | u1.calendar = u2.calendar
}

// one calendar and preference list for each user
// No unowned calendar or preference list occur
fact userCardinality{
	 #Calendar = #User 
	 #PreferenceList = #User
}

// Choose top mobility option in user preferences
/*
fact chooseTopMobilityOption {
	all  u:User ,
		  m : u.calendar.EventList.ChosenMobility,
		  mp: u.mlist.MobilityList | 
		  mp.Priority = min[u.mlist.MobilityList.Priority] 
		  implies m = mp										 

}
*/

fact eachEventIsInCalendar {
	all e : Event  | e in Calendar.EventList 
}
// No overlapping event occur 
// Customized Events are not considered yet
fact noOverlappingEventInCalendar {
	// If the events are not customized, then start time of any event cannot be between start time and end time of any other event
 	no disjoint e, e2 : Calendar.EventList  | e != CustomizedEvent and e2 != CustomizedEvent and
																	gte[e.StartTime, sub[e2.StartTime,e2.ChosenMobility.TravelDuration]] and 
																 	lte[sub[e.StartTime,e.ChosenMobility.TravelDuration] ,e2.EndTime]
	
	no disjoint e1,e2,ce : Calendar.EventList |  e1 != CustomizedEvent and e2 != CustomizedEvent and
																		 ce = CustomizedEvent and gt[e1.StartTime , e2.EndTime] and
																		 lte[ce.StartTime, e2.EndTime] and gte[ce.EndTime , e2.EndTime] and
																		 gt[add[ce.Duration,ce.ChosenMobility.TravelDuration] , sub[sub[e1.StartTime,e1.ChosenMobility.TravelDuration],  e2.EndTime] ]
}


--CHOOSING MOBILITY
--deactivated Mobility cannot be on the PreferenceList
fact onlyActiveMobilitiesOnTheList{ all m:Mobility,p:PreferenceList| m in p.MobilityList <=> m.status=Activated }
 
--Mobility that is not on Preference List cannot be chosen
fact ChosenMobilityMustBeOnPreferenceList{all e:Event,p:PreferenceList|e.ChosenMobility in p.MobilityList}

--Mobility cannot be chosen if the travel time of the event is greater than a given duration Limit
fact ChosenMobilityMeetsDurationConstraint{all m:Mobility, e:Event|m!=e.ChosenMobility => gt[e.ChosenMobility.TravelDuration,m.durationLimit]}

fact NoTravelDurationIfMobilityIsNotChosen{all m:Mobility, e:Event| lt[m.TravelDuration, Zero] => m!=e.ChosenMobility}

/*
fact DeactivatedIfTravelIsNotInRestrictedTime{

	no e : Calendar.EventList , m:e.ChosenMobility | (gte[m.restrictedStartTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedStartTime ,e.StartTime] ) or gte[m.restrictedEndTime, sub[e.StartTime,e.ChosenMobility.TravelDuration]] and 
																 				 lte[m.restrictedEndTime ,e.StartTime]
}
*/

pred RegisterNewUser[u,up,unew:User] {
	up = u + unew
}
pred editEvent [c,cp:Calendar,e :c.EventList, 
		nStartTime: Natural,
		nEndTime: Natural] {
		
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
	no e,ep: Event,u:User, c,c':u.calendar | ep=e and e not in c.EventList and addEvent[c,c',e] and  addEvent[c,c',ep]

}

assert EditEvent {
	all u:User,cp,c: u.calendar, e:c.EventList ,nStartTime:Natural,
		nEndTime: Natural | editEvent [c,cp,e ,nStartTime,
		nEndTime	]  implies c != cp
}
-- TODO
-- Weather eklencek
-- Priority 
--PREDICATES
--pred reachable
--pred IsCalendarFeasible

pred show{
#User = 1
#Event >2 
#CustomizedEvent = 1 
}
run show for 7
//check AddDeleteUndo
//check EditEvent
