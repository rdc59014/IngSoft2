---- MODULE example ----

EXTENDS Integers, TLC

(* --algorithm example

variables x \in 1..5

begin
    Add:
    x := x + 1;

end algorithm; *) 
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..5
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ x' = x + 1
       /\ pc' = "Done"

Next == Add
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
\* Modification History
\* Last modified Sun May 05 09:59:40 ART 2019 by danilo
\* Created Sun May 05 09:23:26 ART 2019 by danilo
