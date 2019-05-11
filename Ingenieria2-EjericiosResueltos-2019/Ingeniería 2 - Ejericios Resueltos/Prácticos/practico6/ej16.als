
// Pág 162 definición de cuantificación acotada

sig Element {}

sig Set {
	elems: set Element
}


pred add[s,s': Set, e: Element] {
	s'.elems = s.elems + e
}

pred union[s1,s2,s': Set] {
	s'.elems = s1.elems+s2.elems
}

pred inter[s1,s2,s':Set] {
	s'.elems = s1.elems & s2.elems
}

pred compl[s,s':Set] {
	s'.elems = univ- s.elems
}


fact SetGenerator {
	some s: Set | no s.elems 
	all s: Set, e: Element | some s': Set | s'.elems = s.elems  + e
}


assert a { // Requiere generación
	all s:Set, e:Element | some s':Set | add[s,s',e]
}

check a

assert u { // Requiere generación
	all s1,s2:Set | some s':Set | union[s1,s2,s']
}

check u


assert i { // Requiere generación
	all s1,s2:Set | some s':Set | inter[s1,s2,s']
}

check i


assert c { // Requiere generación
	all s:Set | some s':Set | compl[s,s']
}

check c

assert Closed {  // Requiere generación
	all s0, s1: Set | some s2: Set | s2.elems = s0.elems + s1.elems
}
check Closed

pred show[]{}

run show
