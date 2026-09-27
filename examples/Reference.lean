/- Semantic counterparts of the core script, using Lean's own kernel. -/
set_option autoImplicit false

namespace LeanTC

def identity (A : Type) (x : A) : A := x

example (A : Type) (a : A) : identity A a = a := rfl
example (A : Type) (B : A → Type) (section_ : (x : A) → B x) (a : A) :
    B a := section_ a

theorem impliesSelf : ∀ (P : Prop), P → P := fun _ p => p
example : Prop := ∀ (P : Prop), P → P
example : Prop := ∀ (_T : Sort 3) (p : Prop), p
example : Sort 4 := ∀ (_ : Sort 3), Type

example (P : Prop) (p q : P) : p = q := rfl
example (P : Prop) (p q : P) (F : P → Type) : F p = F q := rfl
example (A : Type) (B : A → Type) (f : (x : A) → B x) :
    f = (fun x => f x) := rfl
example (A : Type) (a : A) : (let T : Type := A; let x : T := a; identity T x) = a := rfl
example (A : Type) :
    (fun (x : A) => (fun (y : A) => fun (_ : A) => y) x) =
    (fun (outer : A) (_ : A) => outer) := rfl

-- These commands must fail: Type is not its own type, and universes do not lift implicitly.
#check_failure (Type : Type)
#check_failure (fun (A : Type) => (A : Sort 2))
#check_failure (fun (A : Type) (a : A) => a a)

end LeanTC
