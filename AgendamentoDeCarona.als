module carona

open util/ordering[Time]

----------------------------------------SIGNATURES-------------------------------------------------

sig Time {}

sig Car {
	passengers : set Passenger -> Time,
	carpool : set Passenger -> Time
}

one sig UFCG{
	students: set Student
}

abstract sig Student{
	region: Region
}

sig Owner extends Student{
	ownerCar : one Car
}

sig Passenger extends Student{
}

abstract sig Region{ }

one sig Norte,Sul,Leste,Oeste,Centro extends Region{ }

--------------------------------------------FACTS-----------------------------------------------------

fact Passenger{
	
	/*Se um estudante é passegeiro de um carro em um dado momento, em momentos futuros ele pode continuar sendo ou não,
	o mesmo vale para carona*/

	/*Se estudante é passageiro, necessariamente ele faz parte das caronas registradas para um carro*/

	/*Em todos os tempos carros podem ter 0 ou 1 passageiros, 0 ou 1 caronas*/

	/* no segundo tempo de execução todos os estudantes estarao alocados em um carro*/

	/*no último fato não haverá ninguém nos carros e no tempo anterior, todos estarão*/

	all p: Passenger, c: Car, t: Time, tf: t.^next | p in getPassengers[c,t] => (p in getPassengers[c,tf] or passengerNoCar[p,tf] and 
	p in getCarpool[c,t] => (p in getCarpool[c,tf] or passengerNoCarpool[p,tf]))
        
	all p: Passenger, c: Car, t: Time | p in getPassengers[c,t] => p in getCarpool[c,t]
	
	all p: Passenger, t: Time-first | lone p.~(passengers.t)  and lone p.~(carpool.t)

	all p: Passenger, t: first.next | one p.~(passengers.t)

	all p: Passenger, t: last.prev, t': last | one p.~(passengers.t) and no p.~(passengers.t')
}

fact Car{
	
	//Para cada carro só pode haver um dono
	
	//Um carro suporta até 4 passageiros

	//A região do passageiro deve ser a mesma região do dono do carro

	//Os carror podem ter caronas registrados ou não

	all c:Car| #getCarOwner[c] = 1

	all c:Car,t:Time-first| #getPassengers[c,t] < 5

	all  t:Time-first, c: Car | #getPassengers[c,t] > 0 => (getPassengers[c,t].region = getCarOwner[c].region 
        and getCarpool[c,t].region = getCarOwner[c].region)

	all c: Car, t: Time-first | #getCarpool[c,t] >= 0
}

fact UFCG {

	//Todos os estudantes, passageiros ou proprietarios, estarão em UFCG

	all p: Passenger| p in getStudents[]
	all o: Owner| o in getStudents[]
}

fact Region{

	//Toda região está conectada pelo menos a um estudante

	all r: Region | #(r.~region) > 0
}

fact Traces{
	init[first]
	all pre: Time-last | let pos = pre.next |
	some p:Passenger,c:Car | 
	addPassengerInCar[p,c,pre,pos] and 
	addPassengerInCarpool[p,c,pre,pos] or
	removeCarpool[p,c,pre,pos] or
	removePassengers[c,pre,pos]
}

----------------------------------------PREDICATES-------------------------------------------------

pred init[t:Time]{
	all c: Car | no getPassengers[c,t] 
	and no getCarpool[c,t]
}
                                              ----passengers----

//Adiciona o passageiro dentro do carro para locomoção
pred addPassengerInCar[p:Passenger,c:Car,before,after: Time]{
	(passengerNoCar[p,before]) =>
	getPassengers[c,after] = getPassengers[c,before] +p
}

//Verifica se o passageiro não esta no carro
pred passengerNoCar[p: Passenger, t: Time]{
	all c: Car | p !in getPassengers[c,t]
}

//O passageiro chegou ao destino, e retira do carro
pred removePassengers[c:Car, before,after:Time]{
	all p:Passenger | p in c.passengers.before => c.passengers.after = c.passengers.before - p
}

                                            ----carpool---- 
//Adiciona o passageiro no registro de caronas de um carro
pred addPassengerInCarpool[p: Passenger, c: Car, before, after: Time]{
	(passengerNoCarpool[p,before]) =>
	getCarpool[c,after] = getCarpool[c,before] + p
}

//Remove o passageiro no registro de caronas de um carro
pred removeCarpool[p:Passenger, c:Car, before,after:Time]{
	((passengerInCarpool[p,before]) =>
	getCarpool[c,after] = getCarpool[c,before] - p) => getPassengers[c,after]=getPassengers[c,before]-p
	
}

//Verifica se o estudante não esta no registro de caronas de um carro
pred passengerNoCarpool[p: Passenger, t: Time]{
	all c: Car | p !in getCarpool[c,t]
}

//Verifica se o estudante esta no registro de caronas de um carro
pred passengerInCarpool[p: Passenger, t: Time]{
	all c: Car | p in getCarpool[c,t]
}



----------------------------------------FUNCTIONS--------------------------------------------------

fun getTimeNextNext[t:Time] : Time{
	((t.next).next & Time)
}

//Retorna todos os estudantes da UFCG, proprietarios e passageiros
fun getStudents[] : set Student{
	((UFCG.students) & (Owner + Passenger))
}

//Retorna todos os passageiros da UFCG
fun getPassengers[c: Car, t: Time] : set Passenger{
	((c.passengers).t & Passenger)
}

//Retorna todos os caronas da UFCG
fun getCarpool[c: Car, t: Time] : set Passenger{
	((c.carpool).t & Passenger)
}

//Retorna o dono de um determinado carro
fun getCarOwner[c: Car] : Owner{
	((c.~ownerCar) & Owner)
}

--------------------------------------------ASSERTS----------------------------------------------------

//Carro não tem mais de 4 passageiros
assert moreThan4{
	!some c:Car, t:Time-first | #(getPassengers[c,t]) > 4
}

//Estudante não está em UFCG
assert notInUFCG{
	!some s:Student | (s !in getStudents[])
}

//Todos passageiros tem a mesma região do proprietário do carro
assert sameRegion {
	all t:Time-first |( all c:Car| (getPassengers[c,t].region = getCarOwner[c].region))
}

----------------------------------------CHECK'S----------------------------------------------------

pred show[]{}

run show for 13 but exactly 5 Owner, exactly 10 Passenger

check moreThan4 for 13

check notInUFCG for 13

check sameRegion for 13
