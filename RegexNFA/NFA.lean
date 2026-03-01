import Mathlib.Data.Finset.Basic

-- Qの冪集合 𝒫(Q) を定義
def PowerSet (Q : Finset Nat) : Type := {S : Finset Nat // S ⊆ Q}

structure NFA (σ : Type) where
  Q : Finset Nat           -- 状態の有限集合
  δ : Nat → Option σ → PowerSet Q  -- 遷移関数 Q × Σ_ε → 𝒫(Q)
  q₀ : Nat                 -- 開始状態
  F : Finset Nat           -- 受理状態の集合
  -- wellformedness条件
  valid_q₀ : q₀ ∈ Q
  valid_F : F ⊆ Q
