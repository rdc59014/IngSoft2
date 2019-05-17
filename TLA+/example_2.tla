----------------------------- MODULE example_2 -----------------------------
EXTENDS Sequences, TLC
(* --algorithm telephone

variables
    to_send = <<1, 2, 3>>,  \* se enviaran los mensajes 1, 2, 3; en orden.
    received = <<>>,  \* secuencia de mensajes ingresados.
    in_transit = {},  \* buffer donde se guardan los mensajes.
    can_send = TRUE;  \* define una bandera para asegurar que el
                      \* mensaje fue recibido. 

begin

    while Len(received) /= 3 do
        \* send y receiver: se realizan concurrentemente
            
        \* send
        if can_send /\ to_send /= <<>> then
            in_transit := in_transit \union {Head(to_send)};
            to_send := Tail(to_send);
            can_send := FALSE;
        end if;
        
        \* receiver
        \* es no determinista: puede recibir el mensaje -
        \* como no hacer nada, con la misma probabilidad.
        either
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
                either
                    can_send := TRUE;
                or
                    skip;
                end either;
                
            end with;
        or
            skip;
        end either;
         
    end while;

assert received = <<1, 2, 3>>;  \* queremos que los mensajes lleguen
                                \* en el mismo orden.
(*
   si bien eliminamos el error de concurrencia al introducir la bandera,
   introducimos otro mas sutil: solamente se puede enviar si la otra
   persona lo ha recibido, pero que pasaria si el mensaje nunca llega?,
   esto es conocido como un error de liveness.
   
   Otra forma seria introducir un "either" dentro del "with", para darle 
   no determinismo a la confirmacion de llegada. Pero esto nos lleva a un
   estado de deadlock, es decir falla la confirmacion.
*)
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES to_send, received, in_transit, can_send, pc

vars == << to_send, received, in_transit, can_send, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ can_send = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF can_send /\ to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                               /\ can_send' = FALSE
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit, can_send >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(received = <<1, 2, 3>>, 
                              "Failure of assertion at line 44, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit, can_send >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
              /\ \/ /\ can_send' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED can_send
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu May 16 15:48:28 ART 2019 by danilo
\* Created Thu May 16 10:44:51 ART 2019 by danilo
