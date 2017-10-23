
// Boolean type is defined
// open util/boolean


// Signatures for the overall sysstem
// All the signatures are defined based on class diagram 

open util/natural

// Necessary Data structures for string and datetime 
sig Str{}

sig DateTime {
	date: one Natural
}

// Signature for events
sig Event{
	StartTime: one DateTime,
	EndTime: one DateTime,
	ChosenMobility: one Mobility,
	periodicity : one Natural,
	name: one Str
}{
one StartTime
one EndTime
lt[StartTime.date , EndTime.date]

}

// Extension for customized events
sig CustomizedEvent extends Event {
	Duration: one Natural
}
{
	one Duration

	lte[Duration , sub[sub[EndTime.date,StartTime.date],ChosenMobility.TravelDuration] ]
}

sig Mobility{
	TravelDuration: one Natural,
	MType: one Str
}
{
	//gt[TravelDuration , 0]
}

sig Calendar {
	EventList: some Event,
	MobilityList = EventList.ChosenMobility
}{
	#EventList = #MobilityList
}

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

sig PreferenceList {
	MobilityList: some Mobility
}
sig Default extends PreferenceList {
	listName : one Str
}
sig CustomizedList extends PreferenceList {}

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

fact eachEventIsInCalendar {
	all e : Event  | e in Calendar.EventList 
}

// No overlapping event occur 
// Customized Events are not considered yet
fact noOverlappingEventInCalendar {
	// If the events are not customized, then start time of any event cannot be between start time and end time of any other event
 	no disjoint e, e2 : Calendar.EventList  | e != CustomizedEvent and e2 != CustomizedEvent and
																	gte[e.StartTime.date, sub[e2.StartTime.date,e2.ChosenMobility.TravelDuration]] and 
																 	lte[sub[e.StartTime.date,e.ChosenMobility.TravelDuration] ,e2.EndTime.date]
	no disjoint e1,e2,ce : Calendar.EventList |  e1 != CustomizedEvent and e2 != CustomizedEvent and
																		 ce = CustomizedEvent and gt[e1.StartTime.date , e2.EndTime.date] and
																		 lte[ce.StartTime.date, e2.EndTime.date] and gte[ce.EndTime.date , e2.EndTime.date] and
																		 gt[add[ce.Duration,ce.ChosenMobility.TravelDuration] , sub[sub[e1.StartTime.date,e1.ChosenMobility.TravelDuration],  e2.EndTime.date] ]
}
fact uniqueMobType {
	no  m1,m2:  Mobility | m1!=m2 and m1.MType = m2.MType
}

pred show{
#User = 1
#Event > 2

}
run show for 5 
