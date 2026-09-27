prelude

mutual
  inductive Tree : Type where
    | node : Forest → Tree
  inductive Forest : Type where
    | nil : Forest
    | cons : Tree → Forest → Forest
end
