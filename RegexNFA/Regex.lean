import Mathlib.Data.Set.Basic

inductive Regex (σ : Type) where
  | empty
  | epsilon
  | char (a : σ)
  | alt (r1 r2 : Regex σ)
  | seq (r1 r2 : Regex σ)
  | star (r : Regex σ)


inductive Regex.Matches : Regex σ → List σ → Prop where
  -- empty: 何も受理しない（コンストラクタなし）
  | epsilon : Matches epsilon []
  | char : Matches (char a) [a]
  | altLeft : Matches r1 w → Matches (alt r1 r2) w
  | altRight : Matches r2 w → Matches (alt r1 r2) w
  | seq : Matches r1 w1 → Matches r2 w2 → Matches (seq r1 r2) (w1 ++ w2)
  | starEmpty : Matches (star r) []
  | starConcat : w1 ≠ [] → Matches r w1 → Matches (star r) w2 →
                Matches (star r) (w1 ++ w2)

notation:50 r " ~ " w => Regex.Matches r w
