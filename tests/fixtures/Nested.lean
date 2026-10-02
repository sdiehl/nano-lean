import Init

namespace NestedFixture

inductive Tree (α : Type u) : Type u where
  | leaf : α → Tree α
  | branch : List (Tree α) → Tree α

-- The list auxiliary recursor has one enclosing parameter here.
noncomputable def size {α : Type u} (t : Tree α) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ => 1) (fun _ n => n) 0 (fun _ _ n ns => n + ns) t

theorem computation : size (Tree.branch [Tree.leaf 3, Tree.leaf 4]) = 2 := rfl

-- No enclosing parameters: the list constructor still has its own parameter.
inductive Rose : Type where
  | node : List Rose → Rose

theorem empty : Rose.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ n => n + 1) 0 (fun _ _ n ns => n + ns) (Rose.node []) = 1 := rfl

end NestedFixture

namespace NestedFixture

-- Successive specializations exercise more than one auxiliary family.
inductive Deep : Type where
  | flat : List Deep → Deep
  | node : List (List Deep) → Deep

inductive PairTree (α β : Type u) : Type u where
  | leaf : α → β → PairTree α β
  | branch : List (PairTree α β) → PairTree α β

mutual
  inductive Lefts (α : Type u) : Type u where
    | nil : Lefts α
    | cons : α → Rights α → Lefts α
  inductive Rights (α : Type u) : Type u where
    | cons : α → Lefts α → Rights α
end

inductive MutualContainer : Type where
  | node : Lefts MutualContainer → MutualContainer

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

inductive IndexedContainer : Type where
  | node (n : Nat) : Vec IndexedContainer n → IndexedContainer

inductive FunctionContainer : Type where
  | node : (Bool → List FunctionContainer) → FunctionContainer

end NestedFixture
