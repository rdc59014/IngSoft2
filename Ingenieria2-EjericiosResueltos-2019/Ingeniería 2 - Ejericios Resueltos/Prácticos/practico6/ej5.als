sig Elem {}

sig Rel {
	elems: set Elem,
	rel: elems->elems
}


pred preorder[r: Rel] {
	//all a,b,c: r.elems | (a->a) in r.rel and (   ((a->b) in r.rel and (b->c) in r.rel) => (a->c) in r.rel  )
    r.elems <: iden  in r.rel and (r.rel).(r.rel) in r.rel
}


pred partial_order[r:Rel] {
	preorder[r]  and  all a,b: r.elems | ((a->b) in r.rel and (b->a) in r.rel) => (a=b)

}

pred total_order[r:Rel] {
	partial_order[r] and all a,b: r.elems | (a->b) in r.rel or (b->a) in r.rel

}

pred strict_order[r:Rel] {
	 (r.rel).(r.rel) in r.rel and 
						all a,b: r.elems | (((a->b) in r.rel and (b->a) in r.rel) => (a=b)) and (a->a) not in r.rel

}

pred first_elem[r:Rel] {
	some a: r.elems | all b: r.elems | (b->a) in r.rel => a=b
}

pred last_elem[r:Rel] {
	some a: r.elems | all b: r.elems | (a->b) in r.rel => a=b
}

assert parcialestotal {
	all r: Rel | partial_order[r]=>total_order[r]
}

assert primerelem {
	all r: Rel | partial_order[r] => first_elem[r]
}

assert unionorderstrict {
	all r,s: Rel | (strict_order[r] and strict_order[s]) => strict_order[r+s]
}

assert joinorderstrict {
	all r,s: Rel | some  t: Rel | t.elems = (r.elems)+(s.elems) and t.rel = (r.rel).(s.rel) and (strict_order[r] and 
																														strict_order[s]) =>   strict_order[t]
}

check joinorderstrict
run first_elem for 3 but 1 Rel
