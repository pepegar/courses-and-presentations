\* Modified from Hillel Wayne's in https://learntla.com/intro/conceptual-overview.html
---- MODULE overdraft ----
EXTENDS TLC, Integers

People == {"alice", "bob"}
Money == 1..2

(* --algorithm overdraft
variables
  accounts \in [People -> Money];

define
    \* Invariants are values that are checked in every state of our progam.
    NoOverdrafts ==
        \* for all p in People. (notice that lots of math operations in TLA+ use LaTeX notation)
        \A p \in People:
            \* the account of p must be greater than zero
            accounts[p] >= 0 \* TODO: see what happens if we make it mandatory for all accounts to have at least 1$
end define;

\* TODO: see what happens if we allow concurrent wire transfers
process wire \in 1
variable
  amount \in 1..2;
  from \in People;
  to \in People
begin
  Check:
    if accounts[from] >= amount /\ from /= to then
      Withdraw:
        accounts[from] := accounts[from] - amount;
      Deposit:
        accounts[to] := accounts[to] + amount;
    end if;
end process;
end algorithm; *)
====
