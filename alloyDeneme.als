open util/integer


sig Str{}

/* sig datetime{
	dateTime: one Int,
        --availability: one Bool
}{dateTime>0}*/

sig Calendar {
	EventList: some Event,
	MobilityList = EventList.ChosenMobility
}{
	#EventList = #MobilityList
}

sig Event{
	name: one Str,
	startofTime:one Int ,
	endofTime:one Int,
	ChosenMobility: one MobilityOption,	
	location:one Str,
	repeat:one Str
}{
    one startofTime
    one endofTime
    startofTime<endofTime
    startofTime>0
    endofTime>0
   }

sig Break extends Event{
	duration:one Int,
	frequency: one Str
}{one frequency
    one duration
    duration>0
    duration <=minus[minus[endofTime,startofTime],ChosenMobility.travelTime] 
	}


sig User {
	username: one Str,
	password: one Str,
	preferredMobilities: one PreferenceList,
	calendar: one Calendar
	     }{one Calendar
	one preferredMobilities}

abstract sig mobilityStatus {}
one sig Activated extends mobilityStatus{}
one sig Deactivated extends mobilityStatus{}

abstract sig MobilityOption{
	durationLimit: lone Int,
	status: one mobilityStatus,	
	travelTime:lone Int
}
{durationLimit>=0
    travelTime>=0
}

one sig Car,Tram,Train,Metro,Bus,Bike,Walk extends MobilityOption{}


sig PreferenceList {
	Mobilities: some MobilityOption
}


--FACTS

fact UserNameUnique{
	no disjoint u1,u2:User|u1.username&u2.username!=none
}

fact passwordUnique{
	no disjoint u1,u2:User|u1.password&u2.password!=none
}


--Each User has only one Calendar and one PreferenceList
fact userCardinality{
	 #Calendar = #User 
	 #PreferenceList = #User

}

--All Created Events are in the Calender EventList
fact eachEventIsInCalendar {
	all e : Event  | e in Calendar.EventList 
}


// No overlapping event occur 
// Customized Events are not considered yet
fact noOverlappingEventInCalendar {
	// If the events are not customized, then start time of any event cannot be between start time and end time of any other event
 	no disjoint e, e2 : Calendar.EventList  | e !=Break and e2 != Break and
																	gte[e.startofTime, minus[e2.startofTime,e2.ChosenMobility.travelTime]] and 
																 	lte[minus[e.startofTime,e.ChosenMobility.travelTime] ,e2.endofTime]
	no disjoint e1,e2,ce : Calendar.EventList |  e1 != Break and e2 != Break and
																		 ce = Break and e1.startofTime> e2.endofTime and
																		 plus[ce.duration,ce.ChosenMobility.travelTime] > minus[minus[e1.startofTime,e1.ChosenMobility.travelTime],  e2.endofTime] 
																		
	/*no disjoint e2,ce : Calendar.EventList | e2 != Break and  ce=Break           and             ce.startofTime<e2.endofTime and
																       gte[ce.startofTime, minus[e2.startofTime,e2.ChosenMobility.travelTime]] and 
																 	lte[minus[ce.startofTime,ce.ChosenMobility.travelTime] ,e2.endofTime]*/
	--no disjoint e1,e2,ce : Calendar.EventList |  e1 != Break and e2 != Break and (e1.startofTime&e2.startofTime&ce.startofTime=none)
}

--CHOOSING MOBILITY
--deactivated Mobility cannot be on the PreferenceList
fact onlyActiveMobilitiesOnTheList{ all m:MobilityOption,p:PreferenceList| m in p.Mobilities <=> m.status=Activated }
 
--Mobility that is not on Preference List cannot be chosen
fact ChosenMobilityMustBeOnPreferenceList{all e:Event,p:PreferenceList|e.ChosenMobility in p.Mobilities}

--Mobility cannot be chosen if the travel time of the event is greater than a given duration Limit
fact ChosenMobilityMeetsDurationConstraint{all m:MobilityOption, e:Event|m!=e.ChosenMobility => e.ChosenMobility.travelTime>m.durationLimit}

fact NoTravelDurationIfMobilityIsNotChosen{all m:MobilityOption, e:Event|m.travelTime<0 => m!=e.ChosenMobility}


--PREDICATES
--pred IsDateAvailable
--pred reachable
--pred removeEvent
--pred addEvent





pred Show{ 
#User = 1
 Car.status=Deactivated
 Walk.durationLimit=1
}
run Show for 10
--run IsDateAvailable for 10
