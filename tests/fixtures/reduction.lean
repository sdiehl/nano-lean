import Init
namespace PhaseTwo
structure Operation where
  apply : Nat → Nat → Nat
def subtraction : Operation := ⟨Nat.sub⟩
def direct (n : Nat) := Nat.sub n 4294967296
def projected (n : Nat) := subtraction.apply n 4294967296
def ignore (_ : Nat) : Nat := 0
theorem erased : ignore 1 = ignore 2 := rfl
def erasedCostly := ignore (@Nat.rec (fun _ => Nat) 0 (fun _ x => x) 100000)
def erasedOne := ignore 1
end PhaseTwo
