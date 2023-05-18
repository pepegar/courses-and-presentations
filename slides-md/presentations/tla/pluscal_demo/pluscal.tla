\* Modified from Hillel Wayne's in https://learntla.com/intro/conceptual-overview.html
---- MODULE pluscal ----
EXTENDS TLC, Integers

People == {"alice", "bob"}
Money == 1..2

(* --algorithm pluscal
variables
  acct \in [People -> Money];

define
  NoOverdrafts ==
    \A p \in People:
      acct[p] >= 0
end define;

process wire \in {1}
variable
  amnt \in 1..2;
  from \in People;
  to \in People
begin
  Check:
    if acct[from] >= amnt /\ from /= to then
      Withdraw:
        acct[from] := acct[from] - amnt;
      Deposit:
        acct[to] := acct[to] + amnt;
    end if;
end process;
end algorithm; *)
====
