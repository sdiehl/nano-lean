import Lean

namespace TheoremReductionFixture

theorem conjunction : True ∧ True := ⟨True.intro, True.intro⟩

def fromTheorem : Nat := And.rec (fun _ _ => 7) conjunction

theorem sameConjunction (h : True ∧ True) : True ∧ True := h

def consumeConjunction (h : True ∧ True) : Nat := And.rec (fun _ _ => 7) h

-- Reusing the outer proof argument while reducing sameConjunction would loop.
def fromAlias : Nat := consumeConjunction (sameConjunction conjunction)

theorem delayedRefl : (0 : Nat) = 0 :=
  Nat.rec (motive := fun _ => (0 : Nat) = 0) rfl (fun _ h => h) 1000000000

-- K reduction needs the equality's type, not this enormous proof computation.
def fromEquality : Nat := @Eq.rec Nat 0 (fun _ _ => Nat) 7 0 delayedRefl

theorem sameFalse (h : False) : False := h

def fromFalse (h : False) : Nat := False.elim (sameFalse h)

theorem fromFalse_eq (h : False) : fromFalse h = False.elim h := rfl

-- Submit the reflexivity proof directly to Lean's kernel. The elaborator treats
-- theorem bodies as opaque, but kernel reduction can unfold them.
open Lean Elab Command in
run_elab do
  let nat := mkConst ``Nat
  let seven := mkNatLit 7
  for (source, target) in #[
      (``fromTheorem, `TheoremReductionFixture.fromTheorem_eq),
      (``fromAlias, `TheoremReductionFixture.fromAlias_eq),
      (``fromEquality, `TheoremReductionFixture.fromEquality_eq)] do
    addDecl <| .thmDecl {
      name := target
      levelParams := []
      type := mkApp3 (mkConst ``Eq [levelOne]) nat (mkConst source) seven
      value := mkApp2 (mkConst ``Eq.refl [levelOne]) nat seven
    }

end TheoremReductionFixture
