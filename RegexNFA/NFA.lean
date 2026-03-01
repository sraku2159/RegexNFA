import Mathlib.Data.Finset.Basic

-- Qの冪集合 P(Q) を定義
def PowerSet (Q : Finset Nat) : Type := {S : Finset Nat // S ⊆ Q}

structure NFA (σ : Type) where
  Q : Finset Nat           -- 状態の有限集合
  δ : Nat → Option σ → PowerSet Q  -- 遷移関数 Q × Σ_ε → 𝒫(Q)
  q₀ : Nat                 -- 開始状態
  F : Finset Nat           -- 受理状態の集合
  -- wellformedness条件
  valid_q₀ : q₀ ∈ Q
  valid_F : F ⊆ Q

-- NFAの実行トレース：状態qから文字列wを読んで状態q'に到達できる
inductive NFA.Run : NFA σ → Nat → List σ → Nat → Prop where
  | refl : q ∈ nfa.Q → Run nfa q [] q
  | eps : Run nfa q w q' → q'' ∈ (nfa.δ q' none).val → Run nfa q w q''
  | step : Run nfa q w q' → q'' ∈ (nfa.δ q' (some a)).val →
          Run nfa q (w ++ [a]) q''

-- NFAが文字列wを受理する：初期状態から始めてwを読み、受理状態に到達できる
def NFA.Accepts (nfa : NFA σ) (w : List σ) : Prop :=
  ∃ qf, qf ∈ nfa.F ∧ Run nfa nfa.q₀ w qf

-- 便利な記法
notation:50 nfa " ~ " w => NFA.Accepts nfa w
