sig Node {}
sig Tree {
	parent: Node->Node,
	root: one Node
} {
	no (^parent & iden)
	~parent.parent in iden
	all n:Node | no parent.n => n=root

}



pred show[]{

}

run show for 6 but 1 Tree
