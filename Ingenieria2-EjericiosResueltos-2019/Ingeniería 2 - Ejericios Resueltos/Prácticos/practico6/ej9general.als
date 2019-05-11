open util/ordering[State] 

// En esta versión se considera que no es sólo Indiana el que puede cruzar para llevar a todos.

abstract sig Person { time: Int }

abstract sig Linterna {}
 
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
	time: Int,
	linternan: lone Linterna,
	linternaf: lone Linterna
} {
	(some linternan => no linternaf) && (some linternaf => no linternan)
}


// Estado inicial
fact initialState {
	let s0 = first[] | s0.near = Person && no s0.far  && s0.time = 0 && some s0.linternan
}

// Transición

pred crossBridge [ from, from', to, to': set Person, t, t': Int ] { 
	 some person: from | some person2: from |
		//person!=person2 &&
		from' = from - person - person2 &&
		to' = to   + person + person2 &&
		t' = plus[t, person.time]
} 

fact stateTransition {
	all s: State, s': next[s] |
		(some linternan => (crossBridge [ s.near, s'.near, s.far, s'.far, s.time, s'.time ]  and some s'.linternaf)) &&
		(some linternaf => (crossBridge [ s.far, s'.far,  s.near, s'.near, s.time, s'.time ] and some s'.linternan) )

}

// Estado Final

pred solvePuzzle[] {
	last[].far = Person && (last[].time=<60)
}

// Ejecución

run solvePuzzle for 6 but 10 Int
