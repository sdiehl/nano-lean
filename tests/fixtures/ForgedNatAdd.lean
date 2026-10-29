-- forged-nat-add.ndjson exports this module with `myadd` renamed to `Nat.add` and appends
-- `contra : False := four_ne_zero (key 2 2)`. Literal folding trusts the name, so every core
-- accepts it, as Lean's kernel does. prelude/nat-add.ndjson exports the real `Nat.add`.
def myadd (_ _ : Nat) : Nat := 0
theorem key (a b : Nat) : myadd a b = 0 := rfl
theorem four_ne_zero : (4 : Nat) = 0 → False := fun h => Nat.noConfusion h
