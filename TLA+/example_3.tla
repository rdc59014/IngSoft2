----MODULE example_3----
EXTENDS Integers, TLC, Sequences, FiniteSets

VARIABLES

    BOOLEAN \in {TRUE, FALSE}

set ++ elem == set \union {elem}
set -- elem == set \ {elem}

Add(a, b) == a + b
Aplly(op(_, _), x, y) == op(x, y)

AllLessThan(set, max) == \A x \in set: x < max

SeqOverlapsSet(seq, set) == \E x \in 1..Len(seq): seq[x] \in set

Xor(A, B) == (~A /\ B) \/ (A /\ ~B)
OtherXor(A, B) == ~A <=> B


\* \A A \in BOOLEAN, B \in BOOLEAN, Xor(A, B) = OtherXor(A, B)
====
