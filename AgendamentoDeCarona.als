module carona

open util/ordering[Time]

sig Car{
	owner : one Owner,
	passengers: set Passenger -> Time
}

abstract sig Student{
	region: one Region
}

sig Owner extends Student{}

sig Passenger extends Student{}

one sig UFCG{
	students: set Student -> Time,
	cars: set Car -> Time
}

abstract sig Region{ }

sig Norte,Sul,Leste,Oeste,Centro extends Region{ }

pred init[t: Time]{
	
	all u: UFCG | no (u.students).t and no (u.cars).t
	all c: Car | no (c.owner).t and no (c.passengers).t
	all s: Student | no (s.region).t
}

pred addRegion[r: Region, s: Student, before, after: Time]{
	
	(r !in (s.region).before)
	(s.region).after = (s.region).before + r
}

pred addStudent[s: Student, u: UFCG, before, after: Time]{
	
	(s !in (u.students).before)
	(u.students).after = (u.students).before + s
}


pred addCar[c: Car, u: UFCG, before, after: Time]{
	
	(c !in (u.cars).before)
	(u.cars).after = (u.cars).before + c
}

pred addOwner[o: Owner, c: Car, before, after: Time]{
	
	(o !in (c.owner).before)
	(c.owner).after = (c.owner).before + o
}

pred addPassenger[p: Passenger, c: Car, before, after: Time]{
	
	(p !in (c.passengers).before)
	(c.passengers).after = (c.passengers).before + p
}

fun getRegion[s: Student, t: Time] : Region{
	
}

fun getPassengers[u: UFCG, t: time] : set Passenger{
	((u.students).t & Passenger)
}

fun getOwners[u: UFCG, t: Time] : set Owner{
	((u.students).t & Owner)
}

fun getCars[u: UFCG, t: Time] : set Car{
	((u.cars).t & Car)
}

fact Student{
	all s: Student | s in UFCG.students
}

fact Car{
	all c: Car | c in UFCG.cars
	all c: Car, t: Time-first | #(c.passengers) <= 4
}

fact Traces{
	/*verificar se "UFCG" pode ser instanciada como "u",
	 ou usar a chamada direta "UFCG"*/
	init[first]
	all pre: Time-last | let pos = pre.next |
	some p: Passenger, o: Owner, c: Car, u: UFCG |
	addStudent[p, u, pre, pos] and
	addStudent[o, u, pre, pos] and
	addCar[c, u, pre, pos] and
	addOwner[o, c, pre, pos] and
	addPassenger[p, o, pre, pos]
}
