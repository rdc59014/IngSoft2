open util/ordering [ System ] 

sig Addr, Data{ }

abstract sig Memory{
	addrs: set Addr,
	map: addrs -> one Data
	}
	
sig MainMemory extends Memory {}

sig Cache extends Memory{
	dirty: set addrs
}

sig System{
	cache: Cache,
	main: MainMemory
}

pred  write[m,m':Memory,d:Data,a:Addr] {
	m'.map = m.map ++ (a->d)
}

pred read [ m: Memory, a: Addr, d: Data ] {
    let d' = m.map[a] | some d' implies d = d'
}

pred init [ s: System ] { no s.cache.map }

fact{
	init[first[]]
	//no (MainMemory & Cache) // Muestra warning porque dice que son obviamente disjuntos.
}

//assert{
fact {
	all s: System | no s.cache.dirty => s.cache.map in s.main.map
}

pred flush[s,s': System]{
	all x: s.cache.dirty | (write[s.main, s'.main, s.cache.map[x], x])
											and 	(s'.cache.dirty = s'.cache.dirty-x)
}

pred load[s, s': System, a: Addr, d: Data]{
	s'.cache.map  = s.cache.map ++ (a->d)
}

pred DirtyInv[s: System] {
	no s.cache.dirty => s.cache.map in s.main.map
}

pred Consistent[s: System] {
	s.cache.map - (s.cache.dirty -> Data) in s.main.map
}


pred checkflush {
	all s,s': System | ( DirtyInv[s] and flush[s,s'] => DirtyInv[s'] ) and Consistent[s] and Consistent[s']
}

pred checkload {
	all s,s': System, a:Addr, d:Data | ( DirtyInv[s] and load[s,s', a, d] => DirtyInv[s'] ) and Consistent[s] and Consistent[s']
}

pred checkloadflush {
	all s,s': System, a:Addr, d:Data | ( DirtyInv[s] and (load[s,s', a, d] and flush[s,s']) => DirtyInv[s'] ) and Consistent[s] and Consistent[s']
}

run checkflush for 5 
run checkload for 5
run checkloadflush for 5 

