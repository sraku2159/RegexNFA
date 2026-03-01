inductive Regex (σ : Type) where
  | empty
  | epsilon
  | char (a : σ)
  | alt (r1 r2 : Regex σ)
  | seq (r1 r2 : Regex σ)
  | star (r : Regex σ)
