---- MODULE event_restoration ----
EXTENDS Integers, TLC

(* --algorithm event_restoration
variables 
    x = 1;

process producer = "producer"
begin
\* TODO
end process;

process consumer = "consumer"
begin
\* TODO
end process

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "23fbe51e" /\ chksum(tla) = "61a7dc27")
VARIABLE x

vars == << x >>

ProcSet == {"producer"} \cup {"consumer"}

Init == (* Global variables *)
        /\ x = 1

Next == producer \/ consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
