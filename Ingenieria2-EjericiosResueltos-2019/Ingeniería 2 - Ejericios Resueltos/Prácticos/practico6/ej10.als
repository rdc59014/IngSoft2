open util/ordering[State] 

abstract sig Torre {
	//numero = Int,
	discos: set Discos
	
}

abstract sig Discos {
	tam: Int,
	arriba:  set Discos,
	abajo:  set Discos,
	//torre = Int
}

one sig d1,d2/*,d3,d4/*,d5,d6,d7,d8 */extends Discos { }
//one sig t1,t2,t3 extends Torres { }

fact { d1.tam=1 and d2.tam=2 /*and d3.tam=3 and d4.tam=4 /*and d5.tam=5 and d6.tam=6 
																																			and d7.tam=7 and d8.tam=8 */}
//fact { t1.=1,t2=2,t3=3}

//todos los discos son de diferente tamaño
fact {all disj d,d': Discos | d.tam !=d'.tam}

//dados dos discos, el más pequeño de ellos siempre está por encima del otro.
fact {all disj d,d': Discos | some t: Torre | (d in t.discos and d' in t.discos and (d.tam > d'.tam))
						implies
					    ((d in d'.abajo) and (d' in d.arriba))													
}

pred CambiarPosicion[ d: Discos, t,t':Torre ] {
	//d.torre = t'.numero
	t'.discos = t'.discos + d  
	t.discos = t.discos - d
	all d': Discos | d' in t.discos and d' in d.abajo => (d'.arriba = d'.arriba - d)
	all d': Discos | d' in t'.discos and d' in d.abajo => (d'.arriba = d'.arriba + d)
	d.abajo = t'.discos - d
}



sig State {
	t1: Torre, 
	t2: Torre,
	t3: Torre
} 

// Estado inicial
fact initialState {
	let s0 = first[] | s0.t1.discos = Discos and s0.t2.discos=none and s0.t3.discos=none
}

// Estado Final
pred solvePuzzle[] {
	let sf = last[]  | sf.t1.discos = none and (sf.t2.discos = Discos or sf.t3.discos = Discos)
}

fact stateTransition {
	all s: State, s': next[s] |
					some t, t': Torre, d: Discos |  d in t.discos and d.arriba=none and CambiarPosicion[d, t, t'] and 
											   (( t=s.t1 and t'=s.t2 )
													 => (CambiarPosicion[d, t, t'] and s'.t1=t and s'.t2=t' and s'.t3=s.t3)) 
												and
											   (( t=s.t1 and t'=s.t3 )
													 => (CambiarPosicion[d, t, t'] and s'.t1=t and s'.t2=s.t2 and s'.t3=t')) 
												and
											   (( t=s.t2 and t'=s.t3 )
													 => (CambiarPosicion[d, t, t'] and s'.t1=s.t1 and s'.t2=t and s'.t3=t')) 
												and
											   (( t=s.t3 and t'=s.t1 )
													 => (CambiarPosicion[d, t, t'] and s'.t1=t' and s'.t2=s.t2 and s'.t3=t)) 
												and
											   (( t=s.t3 and t'=s.t2 )
													 => (CambiarPosicion[d, t, t'] and s'.t1=s.t1 and s'.t2=t' and s'.t3=t))
}


// Ejecución

run solvePuzzle for 4
