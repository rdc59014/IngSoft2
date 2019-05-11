sig Vertex { }

sig Graph {
	vertices: set Vertex,
	edges: vertices -> vertices
}


pred acyclic[g: Graph] {
	^(g.edges) & iden = none->none
}


pred not_directed[g: Graph] {
	g.edges = ~(g.edges)
}

pred strongly_connected[g: Graph] {
	(univ->univ) in ^(g.edges)
}

pred connected[g: Graph] {
	all n: g.vertices | all m: g.vertices | n->m in ^(g.edges) or m->n in ^(g.edges)
}


// Existe algún subconjunto de edges que cumple strongly connected
pred component_strongly_connected[g: Graph] {
	// Esto debería ser algo como "some c in g.edges" donde c sea subsets de g.edges
	// some c: set g.edges  | (univ . *c) <: (univ->univ) in ^c  // intento
	// some c: set g.edges  | some v: set g.vertices | (v -> v) in ^c   // intento
	some v: set g.vertices | some v && (v -> v) in ^(g.edges & (v -> v)) && 
(all n: v | all m: g.vertices-v | (not m->n in g.edges-(v->v)) &&
 (not n->m in g.edges-(v->v))  ) // se chequea que los vértices no estén en otras aristas.
}


pred component_connected[g: Graph] {
	some v: set g.vertices | some v && (	all n: v | all m: v | n->m in ^(g.edges & (v -> v)) or m->n in ^(g.edges & (v -> v)))  
&& (all n: v | all m: g.vertices-v | (not m->n in ^(g.edges)) && (not n->m in ^(g.edges))  )
}

run component_connected for 3 but 1 Graph
