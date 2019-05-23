----------------------------- MODULE example_1 -----------------------------
EXTENDS Sequences, TLC
(* --algorithm telefono

variables
    para_enviar = <<1, 2, 3>>,\* se envian los mensajes 1, 2, 3; en ese orden.
    recibidos = <<>>,         \* secuencia de mensajes recibidos.
    en_transito = {},         \* conjunto de los mensajes enviados.

begin
    while Len(recibidos) /= 3 do
        \* enviar y recibir: se realizan concurrentemente
            
        \* enviar:
        if para_enviar /= <<>> then
            en_transito := en_transito \union {Head(para_enviar)};
            para_enviar := Tail(para_enviar);
        end if;
        
        \* recibir:
        either
            \* either es no determinista: puede recibir el mensaje -
            \* como no hacer nada "skip", con la misma probabilidad.
            with mensaje \in en_transito do
                recibidos   := Append(recibidos, mensaje);
                en_transito := en_transito \ {mensaje};
            end with;
        or
            skip;
        end either;
         
    end while;

assert recibidos = <<1, 2, 3>>;  \* queremos que los mensajes lleguen
                                 \* en el mismo orden.
end algorithm;*)


\* BEGIN TRANSLATION
VARIABLES para_enviar, recibidos, en_transito, pc

vars == << para_enviar, recibidos, en_transito, pc >>

Init == (* Global variables *)
        /\ para_enviar = <<1, 2, 3>>
        /\ recibidos = <<>>
        /\ en_transito = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(recibidos) /= 3
               THEN /\ IF para_enviar /= <<>>
                          THEN /\ en_transito' = (en_transito \union {Head(para_enviar)})
                               /\ para_enviar' = Tail(para_enviar)
                          ELSE /\ TRUE
                               /\ UNCHANGED << para_enviar, en_transito >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(recibidos = <<1, 2, 3>>, 
                              "Failure of assertion at line 34, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << para_enviar, en_transito >>
         /\ UNCHANGED recibidos

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E mensaje \in en_transito:
              /\ recibidos' = Append(recibidos, mensaje)
              /\ en_transito' = en_transito \ {mensaje}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED para_enviar

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
(*
   si bien eliminamos el error de concurrencia al introducir la bandera,
   introducimos otro mas sutil: solamente se puede enviar si la otra
   persona lo ha recibido, pero que pasaria si el mensaje nunca llega?,
   esto es conocido como un error de liveness.
   
   Otra forma seria introducir un "either" dentro del "with", para darle 
   no determinismo a la confirmacion de llegada. Pero esto nos lleva a un
   estado de deadlock, es decir falla la confirmacion.
*)
====
