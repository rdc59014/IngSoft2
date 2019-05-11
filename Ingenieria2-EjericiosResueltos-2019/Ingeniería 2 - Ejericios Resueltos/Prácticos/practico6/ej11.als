//module tour/addressBook1h ------- Page 14..16

abstract sig Target { }
sig Name, Addr extends Target { }

sig Book1 {
	addr: Name -> lone Addr
}

pred show [b: Book1] {
	#b.addr > 1
	#Name.(b.addr) > 1
}
run show for 3 but 1 Book1

pred add1 [b, b': Book1, n: Name, a: Addr] {
	b'.addr = b.addr + n->a
}

pred del1 [b, b': Book1, n: Name] {
	b'.addr = b.addr - n->Addr
}

fun lookup1 [b: Book1, n: Name] : set Addr {
	n.(b.addr)
}

pred showAdd1 [b, b': Book1, n: Name, a: Addr] {
	add1 [b, b', n, a]
	#Name.(b'.addr) > 1
}
run showAdd1 for 3 but 2 Book1

assert delUndoesAdd1 {
	all b, b', b'': Book1, n: Name, a: Addr |
		no n.(b.addr) and add1 [b, b', n, a] and del1 [b', b'', n]
		implies
		b.addr = b''.addr
}

assert addIdempotent1 {
	all b, b', b'': Book1, n: Name, a: Addr |
		add1 [b, b', n, a] and add1 [b', b'', n, a]
		implies
		b'.addr = b''.addr
}

assert addLocal1 {
	all b, b': Book1, n, n': Name, a: Addr |
		add1 [b, b', n, a] and n != n'
		implies
		lookup1 [b, n'] = lookup1 [b', n']
}

// This command should not find any counterexample.
check delUndoesAdd1 for 3

// This command should not find any counterexample.
check delUndoesAdd1 for 10 but 3 Book1

// This command should not find any counterexample.
check addIdempotent1 for 3

// This command should not find any counterexample.
check addLocal1 for 3 but 2 Book1

------------------------------------ ----------------------------------------------------------------------------------------------------------------------

//module tour/addressBook2e --- this is the final model in Fig 2.14

//abstract sig Target { }
//sig Addr extends Target { }
//abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	names: set Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred add [b, b': Book, n: Name, t: Target] { b'.addr = b.addr + n->t }
pred del [b, b': Book, n: Name, t: Target] { b'.addr = b.addr - n->t }
fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }

assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr
}

// This should not find any counterexample.
check delUndoesAdd for 3

assert addIdempotent {
	all b, b', b'': Book, n: Name, t: Target |
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr
}

// This should not find any counterexample.
check addIdempotent for 3

assert addLocal {
	all b, b': Book, n, n': Name, t: Target |
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}

// This shows a counterexample similar to Fig 2.13
check addLocal for 3 but 2 Book

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}

// This shows a counterexample similar to Fig 2.12
check lookupYields for 4 but 1 Book


-------------- Abstracción  NO FUNCIONA 
fun alpha [b: Book]: Book1 {
    { c: Book1 | c.addr = ^(b.addr) & (Name->Addr) }
}

assert AddOK {
    all c, c': Book, 
        n: Name, a: Addr, /*t: Alias ,*/ b, b': Book1 |
           ( add[c,c',n,a] and //add[c',c'', t, a] and 
             b = alpha[c] and b' = alpha[c'] )
           =>
              add1[b,b',n,a] 
   }

check AddOK
