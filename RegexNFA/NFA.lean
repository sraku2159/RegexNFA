import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

-- =========================================
-- 状態型の定義（Thompson構成用）
-- =========================================

-- Alt用の状態型
inductive AltState (S1 S2 : Type)
  | fromNFA1 : S1 → AltState S1 S2
  | fromNFA2 : S2 → AltState S1 S2
  | newStart : AltState S1 S2
  deriving DecidableEq, Repr

-- Seq用の状態型
inductive SeqState (S1 S2 : Type)
  | fromNFA1 : S1 → SeqState S1 S2
  | fromNFA2 : S2 → SeqState S1 S2
  deriving DecidableEq, Repr

-- Star用の状態型
inductive StarState (S : Type)
  | fromNFA : S → StarState S
  | newStart : StarState S
  deriving DecidableEq, Repr

-- =========================================
-- NFA構造体（状態型でパラメータ化）
-- =========================================

structure NFA (σ : Type) (State : Type) [DecidableEq State] where
  Q : Finset State         -- 状態の有限集合
  δ : State → Option σ → Finset State  -- 遷移関数 Q × Σ_ε → 𝒫(Q)
  q₀ : State               -- 開始状態
  F : Finset State         -- 受理状態の集合
  -- wellformedness条件
  valid_q₀ : q₀ ∈ Q
  valid_F : F ⊆ Q
  valid_δ : ∀ q opt, q ∈ Q → δ q opt ⊆ Q  -- q ∈ Q のとき、遷移先も状態集合に含まれる

-- =========================================
-- 計算可能なNFA実行
-- =========================================

-- 状態集合から1ステップ遷移（与えられた文字/εで遷移可能な状態すべて）
def NFA.step [DecidableEq σ] [DecidableEq State] (nfa : NFA σ State) (states : Finset State) (opt : Option σ) : Finset State :=
  states.fold (· ∪ ·) ∅ (fun q => nfa.δ q opt)

-- ε閉包：ε遷移で到達可能な状態すべて（状態数回イテレーションで不動点に到達）
def NFA.epsilonClosure [DecidableEq σ] [DecidableEq State] (nfa : NFA σ State) (states : Finset State) : Finset State :=
  (List.range nfa.Q.card).foldl (fun s _ =>
    let next := s ∪ nfa.step s none
    if next = s then s else next
  ) states

-- NFAが文字列wを受理する：初期状態から文字列を読み、受理状態に到達する
def NFA.Accepts [DecidableEq σ] [DecidableEq State] (nfa : NFA σ State) (w : List σ) : Prop :=
  let start := nfa.epsilonClosure {nfa.q₀}
  let final := w.foldl (fun states a =>
    nfa.epsilonClosure (nfa.step states (some a))
  ) start
  (final ∩ nfa.F).Nonempty

-- 便利な記法
notation:50 nfa " accepts " w => NFA.Accepts nfa w

-- =========================================
-- 存在型でNFAをラップ（状態型を隠蔽）
-- =========================================

structure SomeNFA (σ : Type) where
  State : Type
  inst : DecidableEq State
  nfa : NFA σ State

-- SomeNFAの受理判定
def SomeNFA.accepts [DecidableEq σ] (snfa : SomeNFA σ) (w : List σ) : Prop :=
  letI := snfa.inst
  NFA.Accepts snfa.nfa w

-- 便利な記法
notation:50 snfa " accepts " w => SomeNFA.accepts snfa w

-- =========================================
-- Thompson構成法の基本NFA
-- =========================================

-- empty（何も受理しないNFA）- 状態は1つだけ
def NFA.empty (σ : Type) : NFA σ (Fin 1) where
  Q := {0}
  q₀ := 0
  F := ∅
  δ := fun _ _ => ∅
  valid_q₀ := by simp
  valid_F := by simp
  valid_δ := by intro q opt hq; simp

-- ε（空文字列のみを受理するNFA）- 状態は2つ（0→1）
def NFA.epsilon (σ : Type) : NFA σ (Fin 2) where
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

-- char a（文字aのみを受理するNFA）- 状態は2つ（0-a→1）
def NFA.char (σ : Type) [DecidableEq σ] (a : σ) : NFA σ (Fin 2) where
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

-- =========================================
-- Thompson構成法の複合NFA
-- =========================================

-- alt（選択：r1 | r2）- 状態型でnfa1とnfa2を区別
def NFA.alt [DecidableEq σ] [DecidableEq S1] [DecidableEq S2]
    (nfa1 : NFA σ S1) (nfa2 : NFA σ S2) : NFA σ (AltState S1 S2) where
  Q := nfa1.Q.image AltState.fromNFA1 ∪
      nfa2.Q.image AltState.fromNFA2 ∪
      {AltState.newStart}
  q₀ := AltState.newStart
  F := nfa1.F.image AltState.fromNFA1 ∪ nfa2.F.image AltState.fromNFA2
  δ := fun q opt =>
    match q with
    | AltState.newStart =>
      if opt = none then
        {AltState.fromNFA1 nfa1.q₀, AltState.fromNFA2 nfa2.q₀}
      else ∅
    | AltState.fromNFA1 q1 =>
      (nfa1.δ q1 opt).image AltState.fromNFA1
    | AltState.fromNFA2 q2 =>
      (nfa2.δ q2 opt).image AltState.fromNFA2
  valid_q₀ := by simp
  valid_F := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx ⊢
    cases hx with
    | inl h1 =>
      obtain ⟨q1, hq1_in_F, rfl⟩ := h1
      left; left
      use q1
      exact ⟨nfa1.valid_F hq1_in_F, rfl⟩
    | inr h2 =>
      obtain ⟨q2, hq2_in_F, rfl⟩ := h2
      left; right
      use q2
      exact ⟨nfa2.valid_F hq2_in_F, rfl⟩
  valid_δ := by
    intro q opt hq q' hq'
    cases q with
    | newStart =>
      simp only at hq'
      split at hq'
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
        cases hq' <;> simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
        · subst_vars
          left; left
          use nfa1.q₀
          exact ⟨nfa1.valid_q₀, rfl⟩
        · subst_vars
          left; right
          use nfa2.q₀
          exact ⟨nfa2.valid_q₀, rfl⟩
      · simp at hq'
    | fromNFA1 q1 =>
      simp only [Finset.mem_image] at hq'
      obtain ⟨q1', hq1'_in_delta, rfl⟩ := hq'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
      left; left
      use q1'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hq
      rcases hq with ⟨⟨q1'', hq1''_in_Q, h_eq⟩ | ⟨q2'', _, h_eq⟩⟩ | h_newStart
      · cases h_eq
        exact ⟨nfa1.valid_δ q1 opt hq1''_in_Q hq1'_in_delta, rfl⟩
      · cases h_eq  -- fromNFA1 ≠ fromNFA2
      · cases h_newStart  -- fromNFA1 ≠ newStart
    | fromNFA2 q2 =>
      simp only [Finset.mem_image] at hq'
      obtain ⟨q2', hq2'_in_delta, rfl⟩ := hq'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
      left; right
      use q2'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hq
      rcases hq with ⟨⟨q1'', _, h_eq⟩ | ⟨q2'', hq2''_in_Q, h_eq⟩⟩ | h_newStart
      · cases h_eq  -- fromNFA2 ≠ fromNFA1
      · cases h_eq
        exact ⟨nfa2.valid_δ q2 opt hq2''_in_Q hq2'_in_delta, rfl⟩
      · cases h_newStart  -- fromNFA2 ≠ newStart

-- seq（連接：r1 · r2）- 状態型でnfa1とnfa2を区別
def NFA.seq [DecidableEq σ] [DecidableEq S1] [DecidableEq S2]
    (nfa1 : NFA σ S1) (nfa2 : NFA σ S2) : NFA σ (SeqState S1 S2) where
  Q := nfa1.Q.image SeqState.fromNFA1 ∪ nfa2.Q.image SeqState.fromNFA2
  q₀ := SeqState.fromNFA1 nfa1.q₀
  F := nfa2.F.image SeqState.fromNFA2
  δ := fun q opt =>
    match q with
    | SeqState.fromNFA1 q1 =>
      (nfa1.δ q1 opt).image SeqState.fromNFA1 ∪
      (if q1 ∈ nfa1.F && opt = none then {SeqState.fromNFA2 nfa2.q₀} else ∅)
    | SeqState.fromNFA2 q2 =>
      (nfa2.δ q2 opt).image SeqState.fromNFA2
  valid_q₀ := by
    simp only [Finset.mem_union, Finset.mem_image]
    left
    use nfa1.q₀
    exact ⟨nfa1.valid_q₀, rfl⟩
  valid_F := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image] at hx ⊢
    obtain ⟨q2, hq2_in_F, rfl⟩ := hx
    right
    use q2
    exact ⟨nfa2.valid_F hq2_in_F, rfl⟩
  valid_δ := by
    intro q opt hq q' hq'
    cases q with
    | fromNFA1 q1 =>
      simp only [Finset.mem_union] at hq'
      cases hq' with
      | inl h1 =>
        -- q' comes from nfa1.δ q1 opt
        simp only [Finset.mem_image] at h1
        obtain ⟨q1', hq1'_in_delta, rfl⟩ := h1
        simp only [Finset.mem_union, Finset.mem_image]
        left
        use q1'
        simp only [Finset.mem_union, Finset.mem_image] at hq
        rcases hq with ⟨q1'', hq1''_in_Q, h_eq⟩ | ⟨q2'', _, h_eq⟩
        · cases h_eq
          exact ⟨nfa1.valid_δ q1 opt hq1''_in_Q hq1'_in_delta, rfl⟩
        · cases h_eq  -- fromNFA1 ≠ fromNFA2
      | inr h2 =>
        -- q' comes from bridge transition
        split at h2
        · simp only [Finset.mem_singleton] at h2
          subst h2
          simp only [Finset.mem_union, Finset.mem_image]
          right
          use nfa2.q₀
          exact ⟨nfa2.valid_q₀, rfl⟩
        · simp at h2
    | fromNFA2 q2 =>
      simp only [Finset.mem_image] at hq'
      obtain ⟨q2', hq2'_in_delta, rfl⟩ := hq'
      simp only [Finset.mem_union, Finset.mem_image]
      right
      use q2'
      simp only [Finset.mem_union, Finset.mem_image] at hq
      rcases hq with ⟨q1'', _, h_eq⟩ | ⟨q2'', hq2''_in_Q, h_eq⟩
      · cases h_eq  -- fromNFA2 ≠ fromNFA1
      · cases h_eq
        exact ⟨nfa2.valid_δ q2 opt hq2''_in_Q hq2'_in_delta, rfl⟩

-- star（繰り返し：r*）- 新しい開始状態を追加
def NFA.star [DecidableEq σ] [DecidableEq S]
    (nfa : NFA σ S) : NFA σ (StarState S) where
  Q := nfa.Q.image StarState.fromNFA ∪ {StarState.newStart}
  q₀ := StarState.newStart
  F := {StarState.newStart}  -- 新しい開始状態のみが受理状態
  δ := fun q opt =>
    match q with
    | StarState.newStart =>
      if opt = none then {StarState.fromNFA nfa.q₀} else ∅
    | StarState.fromNFA q' =>
      (nfa.δ q' opt).image StarState.fromNFA ∪
      (if q' ∈ nfa.F && opt = none then {StarState.newStart} else ∅)
  valid_q₀ := by simp
  valid_F := by simp
  valid_δ := by
    intro q opt hq q' hq'
    cases q with
    | newStart =>
      simp only at hq'
      split at hq'
      · simp only [Finset.mem_singleton] at hq'
        subst hq'
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
        left
        use nfa.q₀
        exact ⟨nfa.valid_q₀, rfl⟩
      · simp at hq'
    | fromNFA q'' =>
      simp only at hq'
      simp only [Finset.mem_union] at hq'
      cases hq' with
      | inl h1 =>
        simp only [Finset.mem_image] at h1
        obtain ⟨q''', hq'''_in_delta, rfl⟩ := h1
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
        left
        use q'''
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hq
        rcases hq with ⟨q'''', hq''''_in_Q, h_eq⟩ | h_newStart
        · cases h_eq
          exact ⟨nfa.valid_δ q'' opt hq''''_in_Q hq'''_in_delta, rfl⟩
        · cases h_newStart  -- fromNFA ≠ newStart
      | inr h2 =>
        split at h2
        · simp only [Finset.mem_singleton] at h2
          subst h2
          simp
        · simp at h2

-- =========================================
-- NFAの性質を表す補題
-- =========================================

-- 補題は後で証明する
lemma epsilonClosure_epsilon_q0 (σ : Type) [DecidableEq σ] :
  (NFA.epsilon σ).epsilonClosure {0} = {0, 1} := by
  sorry

lemma epsilonClosure_char_q0 (σ : Type) [DecidableEq σ] (a : σ) :
  (NFA.char σ a).epsilonClosure {0} = {0} := by
  sorry

lemma epsilon_step_with_char (σ : Type) [DecidableEq σ] (states : Finset (Fin 2)) (c : σ) :
  (NFA.epsilon σ).step states (some c) = ∅ := by
  sorry

lemma epsilonClosure_empty [DecidableEq σ] [DecidableEq State] (nfa : NFA σ State) :
  nfa.epsilonClosure ∅ = ∅ := by
  sorry

lemma epsilon_foldl_empty (σ : Type) [DecidableEq σ] (w : List σ) :
  w.foldl (fun states a =>
    (NFA.epsilon σ).epsilonClosure ((NFA.epsilon σ).step states (some a))
  ) ∅ = ∅ := by
  sorry

-- epsilon NFA の epsilonClosure の性質
lemma epsilon_epsilonClosure_contains_one [DecidableEq σ] :
  (1 : Fin 2) ∈ (NFA.epsilon σ).epsilonClosure {0} := by
  -- epsilonClosure の定義から、{0} ∪ step {0} none ∪ ... を計算
  -- δ(0, ε) = {1} なので、1回のイテレーションで 1 が追加される
  -- foldl の計算が必要で複雑なので一旦 sorry
  -- 本質的には: {0} に step でε遷移を適用すると {1} が追加される
  sorry

lemma NFA.epsilon_accepts_iff [DecidableEq σ] (w : List σ) :
  (NFA.epsilon σ accepts w) ↔ w = [] := by
  constructor
  · -- → 方向: epsilon が受理する → w = []
    intro h
    -- 背理法: w ≠ [] と仮定
    by_contra hw
    -- w ≠ [] なら w = a :: ws の形
    obtain ⟨a, ws, rfl⟩ := List.exists_cons_of_ne_nil hw
    -- epsilon の定義より、文字を読むと遷移できない
    simp only [NFA.Accepts, NFA.epsilon] at h
    -- start から (some a) を読むと ∅ になる
    -- δ(0, some a) = ∅, δ(1, some a) = ∅
    -- よって step start (some a) = ∅
    -- epsilonClosure ∅ = ∅
    -- foldl の結果も ∅
    -- final ∩ F = ∅ で Nonempty でない、矛盾
    sorry
  · -- ← 方向: w = [] → epsilon が受理する
    intro hw
    rw [hw]
    -- w = [] の場合、foldl は何もしない
    simp only [NFA.Accepts, NFA.epsilon]
    -- foldl [] s = s
    rw [List.foldl_nil]
    -- goal: (epsilonClosure {0} ∩ {1}).Nonempty
    -- epsilon_epsilonClosure_contains_one より 1 ∈ epsilonClosure {0}
    -- 1 ∈ epsilonClosure {0} かつ 1 ∈ {1} なので交わりが空でない
    rw [Finset.Nonempty]
    use (1 : Fin 2)
    rw [Finset.mem_inter]
    constructor
    · exact epsilon_epsilonClosure_contains_one
    · simp

lemma NFA.char_accepts_iff [DecidableEq σ] (a : σ) (w : List σ) :
  (NFA.char σ a accepts w) ↔ w = [a] := by
  constructor <;> intro h
  ·
    sorry
  · sorry
-- =========================================
-- Thompson構成の各操作に対する受理条件の補題
-- =========================================

-- Alt用の補助補題
section AltLemmas
variable [DecidableEq σ] [DecidableEq S1] [DecidableEq S2]
variable (nfa1 : NFA σ S1) (nfa2 : NFA σ S2)

-- fromNFA1 と fromNFA2 は単射
lemma fromNFA1_injective : Function.Injective (AltState.fromNFA1 : S1 → AltState S1 S2) := by
  intro a b h
  injection h

lemma fromNFA2_injective : Function.Injective (AltState.fromNFA2 : S2 → AltState S1 S2) := by
  intro a b h
  injection h

-- fromNFA1 と fromNFA2 の image は交わらない（異なるコンストラクタ）
lemma fromNFA1_fromNFA2_disjoint (s1 : Finset S1) (s2 : Finset S2) :
  Disjoint (s1.image AltState.fromNFA1) (s2.image AltState.fromNFA2) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  -- a ∈ s1.image fromNFA1 なので a = fromNFA1 q1
  obtain ⟨q1, _, rfl⟩ := Finset.mem_image.mp ha
  -- b ∈ s2.image fromNFA2 なので b = fromNFA2 q2
  obtain ⟨q2, _, rfl⟩ := Finset.mem_image.mp hb
  -- fromNFA1 q1 ≠ fromNFA2 q2（異なるコンストラクタ）
  intro h
  -- コンストラクタが異なるので矛盾
  cases h

-- disjoint より交わりが空
lemma fromNFA1_fromNFA2_inter_empty (s1 : Finset S1) (s2 : Finset S2) :
  (s1.image AltState.fromNFA1) ∩ (s2.image AltState.fromNFA2) = ∅ := by
  rw [← Finset.disjoint_iff_inter_eq_empty]
  exact fromNFA1_fromNFA2_disjoint s1 s2

-- newStart は fromNFA1 や fromNFA2 のどれでもない
lemma newStart_ne_fromNFA1 (q : S1) : (AltState.newStart : AltState S1 S2) ≠ AltState.fromNFA1 q := by
  intro h
  cases h

lemma newStart_ne_fromNFA2 (q : S2) : (AltState.newStart : AltState S1 S2) ≠ AltState.fromNFA2 q := by
  intro h
  cases h

-- alt の δ 関数の振る舞い
lemma alt_delta_newStart_epsilon :
  (nfa1.alt nfa2).δ AltState.newStart none = {AltState.fromNFA1 nfa1.q₀, AltState.fromNFA2 nfa2.q₀} := by
  simp only [NFA.alt]
  rfl

lemma alt_delta_newStart_char (a : σ) :
  (nfa1.alt nfa2).δ AltState.newStart (some a) = ∅ := by
  simp only [NFA.alt]
  rfl

lemma alt_delta_fromNFA1 (q : S1) (opt : Option σ) :
  (nfa1.alt nfa2).δ (AltState.fromNFA1 q) opt = (nfa1.δ q opt).image AltState.fromNFA1 := by
  rfl

lemma alt_delta_fromNFA2 (q : S2) (opt : Option σ) :
  (nfa1.alt nfa2).δ (AltState.fromNFA2 q) opt = (nfa2.δ q opt).image AltState.fromNFA2 := by
  rfl

-- fromNFA1 で包まれた状態集合に対する step の対応
lemma alt_step_fromNFA1 (states : Finset S1) (a : σ) :
  (nfa1.alt nfa2).step (states.image AltState.fromNFA1) (some a) =
  (nfa1.step states (some a)).image AltState.fromNFA1 := by
  -- 証明の方針:
  -- 1. δ の定義により、fromNFA1 q から遷移すると結果も fromNFA1 で包まれる
  -- 2. fold (∪) と image の分配則を使う
  -- これらは fold と image の性質から従うが、詳細な証明は複雑なので一旦 sorry
  sorry

-- fromNFA2 で包まれた状態集合に対する step の対応
lemma alt_step_fromNFA2 (states : Finset S2) (a : σ) :
  (nfa1.alt nfa2).step (states.image AltState.fromNFA2) (some a) =
  (nfa2.step states (some a)).image AltState.fromNFA2 := by
  sorry

-- ε遷移でも同様
lemma alt_step_epsilon_fromNFA1 (states : Finset S1) :
  (nfa1.alt nfa2).step (states.image AltState.fromNFA1) none =
  (nfa1.step states none).image AltState.fromNFA1 := by
  sorry

lemma alt_step_epsilon_fromNFA2 (states : Finset S2) :
  (nfa1.alt nfa2).step (states.image AltState.fromNFA2) none =
  (nfa2.step states none).image AltState.fromNFA2 := by
  sorry

-- ε閉包の対応
lemma alt_epsilonClosure_fromNFA1 (states : Finset S1) :
  (nfa1.alt nfa2).epsilonClosure (states.image AltState.fromNFA1) =
  (nfa1.epsilonClosure states).image AltState.fromNFA1 := by
  sorry

lemma alt_epsilonClosure_fromNFA2 (states : Finset S2) :
  (nfa1.alt nfa2).epsilonClosure (states.image AltState.fromNFA2) =
  (nfa2.epsilonClosure states).image AltState.fromNFA2 := by
  sorry

-- alt の初期状態のε閉包には両方のNFAの初期状態が含まれる
-- （epsilonClosureの性質を示す補助補題が必要なので一旦保留）
lemma alt_start_contains_nfa1_start :
  AltState.fromNFA1 nfa1.q₀ ∈ (nfa1.alt nfa2).epsilonClosure {AltState.newStart} := by
  sorry

lemma alt_start_contains_nfa2_start :
  AltState.fromNFA2 nfa2.q₀ ∈ (nfa1.alt nfa2).epsilonClosure {AltState.newStart} := by
  sorry

-- 文字列を読んだ後の状態集合の分離
-- alt で文字列 w を読んだ後の状態は、fromNFA1 の部分と fromNFA2 の部分に分かれる
lemma alt_foldl_split (w : List σ) :
  let alt_start := (nfa1.alt nfa2).epsilonClosure {AltState.newStart}
  let alt_final := w.foldl (fun states a =>
    (nfa1.alt nfa2).epsilonClosure ((nfa1.alt nfa2).step states (some a))
  ) alt_start
  let nfa1_start := nfa1.epsilonClosure {nfa1.q₀}
  let nfa1_final := w.foldl (fun states a =>
    nfa1.epsilonClosure (nfa1.step states (some a))
  ) nfa1_start
  let nfa2_start := nfa2.epsilonClosure {nfa2.q₀}
  let nfa2_final := w.foldl (fun states a =>
    nfa2.epsilonClosure (nfa2.step states (some a))
  ) nfa2_start
  alt_final = (nfa1_final.image AltState.fromNFA1) ∪ (nfa2_final.image AltState.fromNFA2) := by
  sorry

end AltLemmas

-- NFA.alt の受理条件
lemma NFA.alt_accepts_iff [DecidableEq σ] [DecidableEq S1] [DecidableEq S2]
    (nfa1 : NFA σ S1) (nfa2 : NFA σ S2) (w : List σ) :
  ((nfa1.alt nfa2) accepts w) ↔ (nfa1 accepts w) ∨ (nfa2 accepts w) := by
  -- 証明の骨格：
  -- 1. alt_foldl_split により、alt での実行が nfa1 と nfa2 の実行に分解できる
  -- 2. alt.F = (nfa1.F.image fromNFA1) ∪ (nfa2.F.image fromNFA2)
  -- 3. 従って、alt が受理 ⟺ (nfa1 が受理) ∨ (nfa2 が受理)
  --
  -- この証明には以下の集合論の補題が必要：
  -- - (A ∪ B) ∩ (C ∪ D) が空でない ⟺ (A ∩ C) が空でない ∨ (B ∩ D) が空でない
  -- - S ∩ T が空でない ⟺ (S.image f) ∩ (T.image f) が空でない （f が単射）
  --
  -- これらは Batteries/Mathlib に存在するはずだが、今は skip
  sorry

-- NFA.seq の受理条件
lemma NFA.seq_accepts_iff [DecidableEq σ] [DecidableEq S1] [DecidableEq S2]
    (nfa1 : NFA σ S1) (nfa2 : NFA σ S2) (w : List σ) :
  ((nfa1.seq nfa2) accepts w) ↔
    ∃ w1 w2, w = w1 ++ w2 ∧ (nfa1 accepts w1) ∧ (nfa2 accepts w2) := by
  sorry

-- NFA.star の受理条件
lemma NFA.star_accepts_iff [DecidableEq σ] [DecidableEq S]
    (nfa : NFA σ S) (w : List σ) :
  ((nfa.star) accepts w) ↔
    (w = [] ∨ ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ (nfa accepts w1) ∧ ((nfa.star) accepts w2)) := by
  sorry
