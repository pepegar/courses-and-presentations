---- MODULE pluscal ----
EXTENDS Integers, TLC

(* --algorithm pluscal

\* Variables define the different states in which your system may be.
variables
 x = 2;

begin
    A:
        x := x + 1;
    B:
        x := x + 1;
end algorithm; *)
====
