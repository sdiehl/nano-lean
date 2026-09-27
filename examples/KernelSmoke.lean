prelude
universe u v w

noncomputable def identity (A : Sort u) (a : A) : A := a

noncomputable def chooseLeft (A : Sort u) (B : Sort v) (a : A) (_b : B) : A := a

noncomputable def compose (A : Sort u) (B : Sort v) (C : Sort w)
    (f : B → C) (g : A → B) (x : A) : C := f (g x)

noncomputable def applyIdentity (A : Sort u) (x : A) : A := identity A x

noncomputable def localType (A : Sort u) (a : A) : A :=
  let B := A
  let b : B := a
  b

theorem implicationSelf (P : Prop) : P → P := fun p => p
