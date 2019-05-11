open util/ordering[State] 

abstract sig Person { time: Int }
 
one sig Indy, Novia, Padre, Suegro
       extends Person { }

fact time { 
	Indy.time = 5 &&
	Novia.time = 10 &&
	Padre.time = 20 &&
	Suegro.time = 25
}


sig State {
	near: set Person, 
	far: set Person,
	time: Int
} 


// Estado inicial
fact initialState {
	let s0 = first[] | s0.near = Person && no s0.far  && s0.time = 0
}

// Transición

pred crossBridge [ from, from', to, to': set Person, t, t': Int ] { 
	 some person: from - Indy |
		from' = from - Indy - person &&
		to' = to  + Indy + person &&
		t' = plus[t, person.time]
} 

fact stateTransition {
	all s: State, s': next[s] |
		( Indy in s.near => crossBridge [ s.near, s'.near, s.far, s'.far, s.time, s'.time ] ) &&
		( Indy in s.far => (s'.near = s.near+Indy && s'.far = s.far-Indy && 
																								s'.time = plus[s.time, Indy.time]) )
}

// Estado Final

pred solvePuzzle[] {
	last[].far = Person && (last[].time=<60)
}

// Ejecución

run solvePuzzle for 6 but 10 Int
