prelude

inductive Counter : Type where
  | zero : Counter
  | succ : Counter → Counter
