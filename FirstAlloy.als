
// Boolean type is defined
// open util/boolean
open util/integer

// Signatures for the overall sysstem
// All the signatures are defined based on class diagram 


// Necessary Data structures for string and datetime 
sig Str{}

sig DateTime {
	date: one Int
}{
	date > 0
}

// Signature for events
sig Event{
	StartTime: one DateTime,
	EndTime: one DateTime,
	ChosenMobility: one Mobility,
	name: one Str
}{
one StartTime
one EndTime
StartTime.date < EndTime.date
}

// Extension for periodic events
sig PeriodicEvent extends Event{
	periodicity : one Int
}
{
	periodicity > 0
}
// Extension for customized events
sig CustomizedEvent extends Event {
	Duration: one Int
}
{
	one Duration
	Duration > 0
	Duration <= minus[EndTime.date,StartTime.date] 
}

sig Mobility{
	TravelDuration: one Int,
	MType: one Str
}
{
	TravelDuration > 0
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

fact userCardinality{
	#User = #Calendar
	#User = #PreferenceList
}

fact eachEventIsInCalendar {
	all e : Event  | e in Calendar.EventList 
}
fact noOverlappingEventInCalendar {
	no disjoint e, e2 : Calendar.EventList  |  e.StartTime.date >= minus[e2.StartTime.date,e2.ChosenMobility.TravelDuration] and minus[e.StartTime.date,e.ChosenMobility.TravelDuration] < e2.EndTime.date
}
fact uniqueMobType {
	no disjoint m1,m2:  Mobility | m1.MType = m2.MType
}
pred show{
#User < 2
#Mobility < 3
#CustomizedEvent > 1
}
run show for 5
