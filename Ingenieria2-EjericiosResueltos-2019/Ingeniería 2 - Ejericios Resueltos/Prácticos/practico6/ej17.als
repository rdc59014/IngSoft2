sig Vertex { }

sig Graph {
	vertices: set Vertex,
	edges: vertices -> vertices -> Int
} {
	all v,w: vertices, i,j:Int | i!=j and (v->w->i) in edges => (not v->w->j in edges)   
}


pred show {

}

run show for 4 but 1 Graph
