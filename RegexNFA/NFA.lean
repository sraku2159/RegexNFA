import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

structure NFA (σ : Type) where
  Q : Finset Nat           -- 状態の有限集合
  δ : Nat → Option σ → Finset Nat  -- 遷移関数 Q × Σ_ε → 𝒫(Q)
  q₀ : Nat                 -- 開始状態
  F : Finset Nat           -- 受理状態の集合
  -- wellformedness条件
  valid_q₀ : q₀ ∈ Q
  valid_F : F ⊆ Q
  valid_δ : ∀ q opt, q ∈ Q → δ q opt ⊆ Q  -- q ∈ Q のとき、遷移先も状態集合に含まれる

-- =========================================
-- 計算可能なNFA実行
-- =========================================

-- 状態集合から1ステップ遷移（与えられた文字/εで遷移可能な状態すべて）
def NFA.step [DecidableEq σ] (nfa : NFA σ) (states : Finset Nat) (opt : Option σ) : Finset Nat :=
  states.fold (· ∪ ·) ∅ (fun q => nfa.δ q opt)

-- ε閉包：ε遷移で到達可能な状態すべて（状態数回イテレーションで不動点に到達）
def NFA.epsilonClosure [DecidableEq σ] (nfa : NFA σ) (states : Finset Nat) : Finset Nat :=
  (List.range nfa.Q.card).foldl (fun s _ =>
    let next := s ∪ nfa.step s none
    if next = s then s else next
  ) states

-- NFAが文字列wを受理する：初期状態から文字列を読み、受理状態に到達する
def NFA.Accepts [DecidableEq σ] (nfa : NFA σ) (w : List σ) : Prop :=
  let start := nfa.epsilonClosure {nfa.q₀}
  let final := w.foldl (fun states a =>
    nfa.epsilonClosure (nfa.step states (some a))
  ) start
  (final ∩ nfa.F).Nonempty

-- 便利な記法
notation:50 nfa " accepts " w => NFA.Accepts nfa w

-- =========================================
-- Thompson構成法の補助補題
-- =========================================

-- シフトされたNFAの遷移先もシフトされた状態集合に含まれる
lemma valid_δ_shifted [DecidableEq σ] (nfa : NFA σ) (offset : Nat) (q opt : _) :
  q ∈ nfa.Q.image (· + offset) →
  ∀ q' ∈ (nfa.δ (q - offset) opt).image (· + offset),
  q' ∈ nfa.Q.image (· + offset) := by
    intro h q' hq'
    simp only [Finset.mem_image] at h hq' ⊢
    obtain ⟨q_orig, hq_orig_in_Q, hq_eq⟩ := h
    obtain ⟨y, hy_in_delta, rfl⟩ := hq'
    use y
    constructor
    · have hq_orig_eq : q_orig = q - offset := by omega
      rw [← hq_orig_eq] at hy_in_delta
      exact nfa.valid_δ q_orig opt hq_orig_in_Q hy_in_delta
    · rfl

-- NFA.altのvalid_δ補助補題：ケース1（newStartからのε遷移）
lemma valid_δ_alt_case1 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q = newStart && opt = none then {nfa1.q₀, nfa2.q₀ + offset2} else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) ∪ {newStart} := by
    intro q' hq'
    split at hq'
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      simp only [Finset.mem_union, Finset.mem_image]
      cases hq' with
      | inl h =>
        subst h
        left; left
        exact nfa1.valid_q₀
      | inr h =>
        subst h
        left; right
        use nfa2.q₀
        exact ⟨nfa2.valid_q₀, rfl⟩
    · simp at hq'

-- NFA.altのvalid_δ補助補題：ケース2（nfa1の遷移）
lemma valid_δ_alt_case2 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa1.Q then nfa1.δ q opt else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) ∪ {newStart} := by
    intro q' hq'
    by_cases h : q ∈ nfa1.Q
    · simp [h] at hq'
      simp only [Finset.mem_union]
      left; left
      exact nfa1.valid_δ q opt h hq'
    · simp [h] at hq'

-- NFA.altのvalid_δ補助補題：ケース3（nfa2のシフトされた遷移）
lemma valid_δ_alt_case3 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa2.Q.image (· + offset2) then
    (nfa2.δ (q - offset2) opt).image (· + offset2) else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) ∪ {newStart} := by
    intro q' hq'
    by_cases h : q ∈ nfa2.Q.image (· + offset2)
    · have : q' ∈ (nfa2.δ (q - offset2) opt).image (· + offset2) := by
        simp only [h, ite_true] at hq'
        exact hq'
      simp only [Finset.mem_union]
      left; right
      exact valid_δ_shifted nfa2 offset2 q opt h q' this
    · simp [h] at hq'

-- NFA.seqのvalid_δ補助補題：ケース1（nfa1の遷移）
lemma valid_δ_seq_case1 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa1.Q then nfa1.δ q opt else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) := by
    intro q' hq'
    by_cases h : q ∈ nfa1.Q
    · simp [h] at hq'
      simp only [Finset.mem_union]
      left
      exact nfa1.valid_δ q opt h hq'
    · simp [h] at hq'

-- NFA.seqのvalid_δ補助補題：ケース2（nfa1.Fからnfa2.q₀へのブリッジ）
lemma valid_δ_seq_case2 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa1.F && opt = none then {nfa2.q₀ + offset2} else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) := by
    intro q' hq'
    split at hq'
    · simp only [Finset.mem_singleton] at hq'
      subst hq'
      simp only [Finset.mem_union, Finset.mem_image]
      right
      use nfa2.q₀
      exact ⟨nfa2.valid_q₀, rfl⟩
    · simp at hq'

-- NFA.seqのvalid_δ補助補題：ケース3（nfa2のシフトされた遷移）
lemma valid_δ_seq_case3 [DecidableEq σ] (nfa1 nfa2 : NFA σ) (offset2 : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa2.Q.image (· + offset2) then
    (nfa2.δ (q - offset2) opt).image (· + offset2) else (∅ : Finset Nat)),
  q' ∈ nfa1.Q ∪ nfa2.Q.image (· + offset2) := by
    intro q' hq'
    by_cases h : q ∈ nfa2.Q.image (· + offset2)
    · have : q' ∈ (nfa2.δ (q - offset2) opt).image (· + offset2) := by
        simp only [h, ite_true] at hq'
        exact hq'
      simp only [Finset.mem_union]
      right
      exact valid_δ_shifted nfa2 offset2 q opt h q' this
    · simp [h] at hq'

-- NFA.starのvalid_δ補助補題：ケース1（newStartからnfa.q₀へのε遷移）
lemma valid_δ_star_case1 [DecidableEq σ] (nfa : NFA σ) (newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q = newStart && opt = none then {nfa.q₀} else (∅ : Finset Nat)),
  q' ∈ nfa.Q ∪ {newStart} := by
    intro q' hq'
    split at hq'
    · simp only [Finset.mem_singleton] at hq'
      subst hq'
      simp only [Finset.mem_union, Finset.mem_singleton]
      left
      exact nfa.valid_q₀
    · simp at hq'

-- NFA.starのvalid_δ補助補題：ケース2（nfaの遷移）
lemma valid_δ_star_case2 [DecidableEq σ] (nfa : NFA σ) (newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa.Q then nfa.δ q opt else (∅ : Finset Nat)),
  q' ∈ nfa.Q ∪ {newStart} := by
    intro q' hq'
    by_cases h : q ∈ nfa.Q
    · simp [h] at hq'
      simp only [Finset.mem_union, Finset.mem_singleton]
      left
      exact nfa.valid_δ q opt h hq'
    · simp [h] at hq'

-- NFA.starのvalid_δ補助補題：ケース3（受理状態からnfa.q₀へのループ）
lemma valid_δ_star_case3 [DecidableEq σ] (nfa : NFA σ) (newStart : Nat) (q : Nat) (opt : Option σ) :
  ∀ q' ∈ (if q ∈ nfa.F && opt = none then {nfa.q₀} else (∅ : Finset Nat)),
  q' ∈ nfa.Q ∪ {newStart} := by
    intro q' hq'
    split at hq'
    · simp only [Finset.mem_singleton] at hq'
      subst hq'
      simp only [Finset.mem_union, Finset.mem_singleton]
      left
      exact nfa.valid_q₀
    · simp at hq'

-- =========================================
-- Thompson構成法の補助関数
-- =========================================

-- empty（何も受理しないNFA）
def NFA.empty [DecidableEq σ] : NFA σ where
  Q := {0}
  q₀ := 0
  F := ∅
  δ := fun _ _ => ∅
  valid_q₀ := by simp
  valid_F := by simp
  valid_δ := by intro q opt hq; simp

-- ε（空文字列のみを受理するNFA）
def NFA.epsilon [DecidableEq σ] : NFA σ where
  Q := {0, 1}
  q₀ := 0
  F := {1}
  δ := fun q opt =>
    if q = 0 && opt = none then
      {1}
    else
      ∅
  valid_q₀ := by simp
  valid_F := by simp
  valid_δ := by intro q opt hq; split <;> simp

-- char a（文字aのみを受理するNFA）
def NFA.char [DecidableEq σ] (a : σ) : NFA σ where
  Q := {0, 1}
  q₀ := 0
  F := {1}
  δ := fun q opt =>
    if q = 0 && opt = some a then
      {1}
    else
      ∅
  valid_q₀ := by simp
  valid_F := by simp
  valid_δ := by intro q opt hq; split <;> simp

-- alt（選択：r1 | r2）
-- Thompson構成法で実装
-- 状態の配置：
-- nfa1の状態: そのまま
-- nfa2の状態: offset2 + 元の状態番号（offset2 = nfa1の状態数）
-- 新しい開始状態: newStart（= offset2 + nfa2の状態数）
def NFA.alt [DecidableEq σ] (nfa1 nfa2 : NFA σ) : NFA σ :=
  -- nfa1の最大状態番号+1をオフセットとして使用
  let max1 := nfa1.Q.sup id
  let offset2 := max1 + 1
  -- 新しい開始状態はすべての状態の後
  let max2_shifted := (nfa2.Q.sup id) + offset2
  let newStart := max2_shifted + 1
  {
    Q := nfa1.Q ∪ nfa2.Q.image (· + offset2) ∪ {newStart}
    q₀ := newStart
    F := nfa1.F ∪ nfa2.F.image (· + offset2)
    δ := fun q opt =>
      -- 新しい開始状態からnfa1.q₀とnfa2.q₀へε遷移
      (if q = newStart && opt = none then {nfa1.q₀, nfa2.q₀ + offset2} else ∅) ∪
      -- nfa1の遷移
      (if q ∈ nfa1.Q then nfa1.δ q opt else ∅) ∪
      -- nfa2の遷移（状態をシフト）
      (if q ∈ nfa2.Q.image (· + offset2) then
        let q2 := q - offset2
        let next := nfa2.δ q2 opt
        next.image (· + offset2)
      else ∅)
    valid_q₀ := by simp only [
      Finset.union_singleton,
      Finset.mem_insert,
      Finset.mem_union,
      Finset.mem_image,
      true_or
    ]
    valid_F := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_image] at hx ⊢
      cases hx with
      | inl h1 =>
        -- x ∈ nfa1.F → x ∈ nfa1.Q
        left
        left
        exact nfa1.valid_F h1
      | inr h2 =>
        -- x ∈ nfa2.F.image (· + offset2)
        obtain ⟨y, hy_in_F, rfl⟩ := h2
        left
        right
        use y
        constructor
        · exact nfa2.valid_F hy_in_F
        · rfl
    valid_δ := by
      intro q opt hq q' hq_in_Q
      simp only [Finset.mem_union] at hq_in_Q
      cases hq_in_Q with
      | inl hq_in_nfa =>
        cases hq_in_nfa with
        | inl hq_in_newnfa => exact valid_δ_alt_case1 nfa1 nfa2 offset2 newStart q opt q' hq_in_newnfa
        | inr hq_in_nfa1 => exact valid_δ_alt_case2 nfa1 nfa2 offset2 newStart q opt q' hq_in_nfa1
      | inr hq_in_nfa2 => exact valid_δ_alt_case3 nfa1 nfa2 offset2 newStart q opt q' hq_in_nfa2
  }

-- seq（連接：r1 · r2）
-- Thompson構成法で実装
-- 状態の配置：
-- nfa1の状態: そのまま
-- nfa2の状態: offset2 + 元の状態番号
-- nfa1の受理状態からnfa2.q₀へε遷移
def NFA.seq [DecidableEq σ] (nfa1 nfa2 : NFA σ) : NFA σ :=
  let max1 := nfa1.Q.sup id
  let offset2 := max1 + 1
  {
    Q := nfa1.Q ∪ nfa2.Q.image (· + offset2)
    q₀ := nfa1.q₀
    F := nfa2.F.image (· + offset2)
    δ := fun q opt =>
      -- nfa1の遷移
      (if q ∈ nfa1.Q then nfa1.δ q opt else ∅) ∪
      -- nfa1の受理状態からnfa2の開始状態へε遷移
      (if q ∈ nfa1.F && opt = none then {nfa2.q₀ + offset2} else ∅) ∪
      -- nfa2の遷移（状態をシフト）
      (if q ∈ nfa2.Q.image (· + offset2) then
        let q2 := q - offset2
        let next := nfa2.δ q2 opt
        next.image (· + offset2)
      else ∅)
    valid_q₀ := by
      simp only [Finset.mem_union]
      left
      exact nfa1.valid_q₀
    valid_F := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_image] at hx ⊢
      obtain ⟨y, hy_in_F, rfl⟩ := hx
      right
      use y
      constructor
      · exact nfa2.valid_F hy_in_F
      · rfl
    valid_δ := by
      intro q opt hq q' hq_in_Q
      simp only [Finset.mem_union] at hq_in_Q
      cases hq_in_Q with
      | inl hq_in_transition =>
        cases hq_in_transition with
        | inl hq_in_nfa1 => exact valid_δ_seq_case1 nfa1 nfa2 offset2 q opt q' hq_in_nfa1
        | inr hq_in_bridge => exact valid_δ_seq_case2 nfa1 nfa2 offset2 q opt q' hq_in_bridge
      | inr hq_in_nfa2 => exact valid_δ_seq_case3 nfa1 nfa2 offset2 q opt q' hq_in_nfa2
  }

-- star（繰り返し：r*）
-- Thompson構成法で実装
-- 状態の配置：
-- nfaの状態: そのまま
-- 新しい開始状態: newStart (cardを使う)
-- 新しい開始状態は受理状態でもある（空文字列を受理）
-- 受理状態から開始状態へε遷移（ループ）
def NFA.star [DecidableEq σ] (nfa : NFA σ) : NFA σ :=
  let maxQ := nfa.Q.sup id
  let newStart := maxQ + 1
  {
    Q := nfa.Q ∪ {newStart}
    q₀ := newStart
    F := nfa.F ∪ {newStart}  -- 新しい開始状態も受理状態
    δ := fun q opt =>
      -- 新しい開始状態から元のnfaの開始状態へε遷移
      (if q = newStart && opt = none then {nfa.q₀} else ∅) ∪
      -- nfaの遷移
      (if q ∈ nfa.Q then nfa.δ q opt else ∅) ∪
      -- 受理状態から元の開始状態へε遷移（ループ）
      (if q ∈ nfa.F && opt = none then {nfa.q₀} else ∅)
    valid_q₀ := by
      simp
    valid_F := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx ⊢
      cases hx with
      | inl h1 =>
        -- x ∈ nfa.F → x ∈ nfa.Q
        left
        exact nfa.valid_F h1
      | inr h2 =>
        -- x = newStart
        right
        exact h2
    valid_δ := by
      intro q opt hq q' hq_in_Q
      simp only [Finset.mem_union] at hq_in_Q
      cases hq_in_Q with
      | inl hq_in_transition =>
        cases hq_in_transition with
        | inl hq_in_newstart => exact valid_δ_star_case1 nfa newStart q opt q' hq_in_newstart
        | inr hq_in_nfa => exact valid_δ_star_case2 nfa newStart q opt q' hq_in_nfa
      | inr hq_in_loop => exact valid_δ_star_case3 nfa newStart q opt q' hq_in_loop
  }

-- =========================================
-- NFAの性質を表す補題
-- =========================================

-- まず、epsilon/charのepsilonClosureの計算結果を補題として示す
lemma epsilonClosure_epsilon_q0 (σ : Type) [DecidableEq σ] :
  (NFA.epsilon (σ := σ)).epsilonClosure {0} = {0, 1} := by
  unfold NFA.epsilonClosure NFA.step NFA.epsilon
  simp [Finset.fold]
  decide

lemma epsilonClosure_char_q0 (σ : Type) [DecidableEq σ] (a : σ) :
  (NFA.char a).epsilonClosure {0} = {0} := by
  unfold NFA.epsilonClosure NFA.step NFA.char
  simp [Finset.fold]
  decide

-- εNFAは文字遷移を持たない
lemma epsilon_step_with_char (σ : Type) [DecidableEq σ] (states : Finset Nat) (c : σ) :
  (NFA.epsilon (σ := σ)).step states (some c) = ∅ := by
  unfold NFA.step NFA.epsilon
  -- δ q (some c) = if q = 0 ∧ some c = none then {1} else ∅
  -- some c ≠ none なので常に ∅
  -- したがって fold (∪) ∅ (fun q => ∅) states = ∅
  simp [Finset.fold_const]

-- 空集合のepsilonClosureは空集合
lemma epsilonClosure_empty (σ : Type) [DecidableEq σ] (nfa : NFA σ) :
  nfa.epsilonClosure ∅ = ∅ := by
  -- List.foldl に対する帰納法が必要で複雑
  sorry

-- 空集合から始まるfoldlは空集合のまま（εNFA専用）
lemma epsilon_foldl_empty (σ : Type) [DecidableEq σ] (w : List σ) :
  w.foldl (fun states a =>
    (NFA.epsilon (σ := σ)).epsilonClosure ((NFA.epsilon (σ := σ)).step states (some a))
  ) ∅ = ∅ := by
  -- List.foldl の帰納法で証明可能だが、epsilonClosure_empty が必要
  sorry

-- NFA.epsilonの性質：空文字列のみを受理
lemma NFA.epsilon_accepts_iff [DecidableEq σ] (w : List σ) :
  (NFA.epsilon accepts w) ↔ w = [] := by
  cases w with
  | nil =>
    unfold Accepts
    simp only [List.foldl]
    -- まず補題を適用（NFA.epsilonを展開する前に）
    have h := epsilonClosure_epsilon_q0 σ
    simp only [NFA.epsilon] at h ⊢
    rw [h]
    -- {0, 1} ∩ {1} = {1} は Nonempty
    decide
  | cons a as =>
    constructor
    · intro h
      unfold Accepts at h
      simp only [List.foldl] at h
      -- start = epsilonClosure {0} = {0, 1}
      have hstart := epsilonClosure_epsilon_q0 σ
      simp only [NFA.epsilon] at hstart h
      rw [hstart] at h
      -- step {0, 1} (some a) = ∅ (εNFAは文字遷移を持たない)
      have hstep := epsilon_step_with_char σ {0, 1} a
      simp only [NFA.epsilon] at hstep
      -- その後は空集合のfoldl（epsilon_foldl_empty使用）
      have hempty := epsilon_foldl_empty σ (a :: as)
      simp only [NFA.epsilon] at hempty
      -- final = ∅, ∅ ∩ {1} = ∅ なので Nonempty は False
      sorry
    · intro h
      -- [] ≠ a :: as
      simp at h

-- NFA.charの性質：文字[a]のみを受理
lemma NFA.char_accepts_iff [DecidableEq σ] (a : σ) (w : List σ) :
  (NFA.char a accepts w) ↔ w = [a] := by
  cases w with
  | nil =>
    unfold Accepts
    simp only [List.foldl]
    have h := epsilonClosure_char_q0 σ a
    simp only [NFA.char] at h ⊢
    rw [h]
    -- {0} ∩ {1} = ∅ なので Nonempty は False
    simp
  | cons b bs =>
    cases bs with
    | nil =>
      constructor
      · intro h
        unfold Accepts at h
        simp only [List.foldl] at h
        -- start = epsilonClosure {0} = {0}
        have hstart := epsilonClosure_char_q0 σ a
        simp only [NFA.char] at hstart h
        rw [hstart] at h
        -- step {0} (some b) で、b = a のとき {1}、b ≠ a のとき ∅
        -- epsilonClosure (step {0} (some b)) で最終状態が決まる
        sorry
      · intro h
        simp at h
        -- h : [b] = [a] なので b = a
        have hstart := epsilonClosure_char_q0 σ a
        subst h
        -- 今 b = a
        unfold Accepts
        simp only [List.foldl, NFA.char] at hstart ⊢
        rw [hstart]
        -- step {0} (some a) = {1}
        -- epsilonClosure {1} = {1}
        -- {1} ∩ {1} = {1} は Nonempty
        sorry
    | cons c cs =>
      constructor
      · intro h
        unfold Accepts at h
        -- 2文字以上なので受理されない
        sorry
      · intro h
        simp at h

-- =========================================
-- Thompson構成の各操作に対する受理条件の補題
-- =========================================

-- NFA.alt の受理条件
lemma NFA.alt_accepts_iff [DecidableEq σ] (nfa1 nfa2 : NFA σ) (w : List σ) :
  ((nfa1.alt nfa2) accepts w) ↔ (nfa1 accepts w) ∨ (nfa2 accepts w) := by
  constructor <;> intro h
  ·
    sorry
  ·
    cases h with
    | inl h1 =>
      -- nfa1 accepts w
      suffices nfa1.F ⊆ (nfa1.alt nfa2).F by
        -- nfa1の受理状態はnfa1.altの受理状態に含まれるので、nfa1がwを受理するならnfa1.altもwを受理する
        sorry
      sorry
    | inr h2 =>
      -- nfa2 accepts w
      sorry

-- NFA.seq の受理条件
lemma NFA.seq_accepts_iff [DecidableEq σ] (nfa1 nfa2 : NFA σ) (w : List σ) :
  ((nfa1.seq nfa2) accepts w) ↔
    ∃ w1 w2, w = w1 ++ w2 ∧ (nfa1 accepts w1) ∧ (nfa2 accepts w2) := by
  sorry

-- NFA.star の受理条件
lemma NFA.star_accepts_iff [DecidableEq σ] (nfa : NFA σ) (w : List σ) :
  ((nfa.star) accepts w) ↔
    (w = [] ∨ ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ (nfa accepts w1) ∧ ((nfa.star) accepts w2)) := by
  sorry
