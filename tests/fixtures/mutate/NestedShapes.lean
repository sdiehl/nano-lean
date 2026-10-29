-- Nested inductive shapes for the weekly mutation campaign in .github/workflows/mutate.yml.
universe u v

inductive Rose (α : Type u) : Type u
  | node : α → List (Rose α) → Rose α

inductive ArrTree : Type
  | node : Array ArrTree → ArrTree

inductive OptList : Type
  | mk : List (Option OptList) → OptList

inductive PairTree (α : Type) : Type
  | leaf : α → PairTree α
  | node : List (PairTree α × PairTree α) → PairTree α

mutual
inductive Even' : Type
  | zero : Even'
  | succ : List Odd' → Even'
inductive Odd' : Type
  | succ : Array Even' → Odd'
end

inductive Term : Type
  | var : Nat → Term
  | app : String → List Term → Term
  | lam : (Nat → Option Term) → Term

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

inductive VTree : Type
  | node : (n : Nat) → Vec VTree n → VTree

inductive Deep : Type
  | mk : List (List (Array (Option Deep))) → Deep

structure Wrap (α : Type u) where
  val : α
  more : List α

inductive SWrap : Type
  | mk : Wrap SWrap → SWrap

inductive Sig : Type
  | mk : (Σ n : Nat, Vec Sig n) → Sig

inductive Univ (α : Sort u) : Type u
  | mk : List (PLift α) → List (Univ α) → Univ α

inductive Ex : Type
  | mk : List (Subtype fun (_ : Ex) => True) → Ex

def Rose.size {α} : Rose α → Nat
  | .node _ cs => 1 + (cs.attach.map fun ⟨c, _⟩ => c.size).sum

def rose_ex : Nat := (Rose.node 1 [Rose.node 2 []]).size
