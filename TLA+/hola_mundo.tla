---- MODULE hola_mundo ----
\* TLA+ code
EXTENDS TLC
(* --algorithm hola_mundo
variables s \in {"Hola", "Mundo !!"};
begin
    A:
      print s;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s \in {"Hola", "Mundo !!"}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "Done"
     /\ s' = s

Next == A
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
\* Modification History
\* Last modified Sun May 05 09:12:48 ART 2019 by danilo
\* Created Sun May 05 09:00:56 ART 2019 by danilo
