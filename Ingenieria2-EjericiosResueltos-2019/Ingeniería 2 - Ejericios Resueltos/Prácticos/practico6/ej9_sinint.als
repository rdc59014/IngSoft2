open util/ordering[State] 


//abstract sig Person { time: Int }
sig Min {}
abstract sig Person { time: set Min }

one sig Indy, Novia, Padre, Suegro
       extends Person { }

/*
fact  { 
	Indy.time = 5
	Novia.time = 10
	Padre.time = 20
	Suegro.time = 25
}
*/
fact  { 
	#(Indy.time) = 5
	#(Novia.time) = 10
	#(Padre.time) = 20
	#(Suegro.time) = 25
}


sig State {
	near: set Person, 
	far: set Person,
	time: set Min // Int
} 


// Estado inicial
fact initialState {
	let s0 = first[] | s0.near = Person && no s0.far  && no s0.time  // && s0.time = 0
}

// Transición

pred crossBridge [ from, from', to, to': set Person, t, t': set Min/*Int*/ ] { 
	 some person: from - Indy |
		from' = from - Indy - person &&
		to' = to  + Indy + person && #(t') = #(t)+#(Indy.time)+#(person.time) //time' = plus[plus[time, Indy.time], person.time]
} 

fact stateTransition {
	all s: State, s': next[s] |
		( Indy in s.near => crossBridge [ s.near, s'.near, s.far, s'.far, s.time, s'.time ] ) &&
		( Indy in s.far => crossBridge [ s.far, s'.far, s.near, s'.near, s.time, s'.time ] )
}

// Estado Final

pred solvePuzzle[] {
	last[].far = Person 
}

// Ejecución

run solvePuzzle for 60 but 8 State 
