import Init

namespace PrimitiveFixture

def huge : Nat := 340282366920938463463374607431768211457

theorem hugeAdd : Nat.add huge huge = 680564733841876926926749214863536422914 := rfl

theorem literalRec : Nat.rec (motive := fun _ => Nat) 7 (fun _ acc => Nat.succ acc) 4 = 11 := rfl

def relation (a b : Nat) : Prop := a = b

def lifted : Nat := Quot.lift (fun x : Nat => x) (fun _ _ h => h) (Quot.mk relation 37)

theorem liftReduction : lifted = 37 := rfl

end PrimitiveFixture
