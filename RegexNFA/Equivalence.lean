import RegexNFA.NFA
import RegexNFA.Regex

-- =========================================
-- 構成的な変換関数（Thompson構成法など）
-- =========================================

-- 正規表現からNFAへの変換（Thompson構成法）
def regex_to_nfa [DecidableEq σ] (r : Regex σ) : NFA σ :=
  match r with
  | .empty => NFA.empty
  | .epsilon => NFA.epsilon
  | .char a => NFA.char a
  | .alt r1 r2 => NFA.alt (regex_to_nfa r1) (regex_to_nfa r2)
  | .seq r1 r2 => NFA.seq (regex_to_nfa r1) (regex_to_nfa r2)
  | .star r => NFA.star (regex_to_nfa r)

-- =========================================
-- 各ケースの補題
-- =========================================

theorem regex_to_nfa_correct_empty [DecidableEq σ] (w : List σ) :
  (Regex.empty ~ w) ↔ (regex_to_nfa Regex.empty accepts w) := by
  constructor
  · intro h; cases h
  · intro h
    unfold regex_to_nfa NFA.Accepts at h
    obtain ⟨qf, hqf_in_F, _⟩ := h
    rw [NFA.empty] at hqf_in_F
    contradiction

theorem regex_to_nfa_correct_epsilon [DecidableEq σ] (w : List σ) :
  (Regex.epsilon ~ w) ↔ (regex_to_nfa Regex.epsilon accepts w) := by
  unfold regex_to_nfa
  rw [NFA.epsilon_accepts_iff]
  constructor
  · intro h
    cases h  -- w = []
    rfl
  · intro h
    rw [h]
    constructor

theorem regex_to_nfa_correct_char [DecidableEq σ] (a : σ) (w : List σ) :
  (Regex.char a ~ w) ↔ (regex_to_nfa (Regex.char a) accepts w) := by
  unfold regex_to_nfa
  rw [NFA.char_accepts_iff]
  constructor
  · intro h
    cases h  -- w = [a]
    rfl
  · intro h
    rw [h]
    constructor

-- alt の正しさ
theorem regex_to_nfa_correct_alt [DecidableEq σ] (r1 r2 : Regex σ) (w : List σ)
  (ih1 : (r1 ~ w) ↔ (regex_to_nfa r1 accepts w))
  (ih2 : (r2 ~ w) ↔ (regex_to_nfa r2 accepts w)) :
  (Regex.alt r1 r2 ~ w) ↔ (regex_to_nfa (Regex.alt r1 r2) accepts w) := by
  unfold regex_to_nfa
  -- NFA.alt_accepts_iff を使う
  rw [NFA.alt_accepts_iff]
  constructor
  · intro h
    cases h with
    | altLeft h1 => left; exact ih1.mp h1
    | altRight h2 => right; exact ih2.mp h2
  · intro h
    cases h with
    | inl h1 => exact Regex.Matches.altLeft (ih1.mpr h1)
    | inr h2 => exact Regex.Matches.altRight (ih2.mpr h2)

-- seq の正しさ
theorem regex_to_nfa_correct_seq [DecidableEq σ] (r1 r2 : Regex σ) (w : List σ)
  (ih1 : ∀ w1, (r1 ~ w1) ↔ (regex_to_nfa r1 accepts w1))
  (ih2 : ∀ w2, (r2 ~ w2) ↔ (regex_to_nfa r2 accepts w2)) :
  (Regex.seq r1 r2 ~ w) ↔ (regex_to_nfa (Regex.seq r1 r2) accepts w) := by
  unfold regex_to_nfa
  -- NFA.seq_accepts_iff を使う
  rw [NFA.seq_accepts_iff]
  constructor
  · intro h
    cases h with
    | seq h1 h2 =>
      use _, _
      constructor
      · rfl
      constructor
      · exact ih1 _ |>.mp h1
      · exact ih2 _ |>.mp h2
  · intro ⟨w1, w2, hw, h1, h2⟩
    rw [← hw]
    exact Regex.Matches.seq (ih1 _ |>.mpr h1) (ih2 _ |>.mpr h2)

-- star の正しさ
theorem regex_to_nfa_correct_star [DecidableEq σ] (r : Regex σ) (w : List σ)
  (ih : ∀ w', (r ~ w') ↔ (regex_to_nfa r accepts w')) :
  (Regex.star r ~ w) ↔ (regex_to_nfa (Regex.star r) accepts w) := by
  unfold regex_to_nfa
  -- NFA.star_accepts_iff を使う
  rw [NFA.star_accepts_iff]
  sorry  -- star のマッチング定義が複雑なので一旦 sorry

-- メイン定理：各ケースの補題を使用
theorem regex_to_nfa_correct [DecidableEq σ] (r : Regex σ) :
  ∀ w : List σ, (r ~ w) ↔ ((regex_to_nfa r) accepts w) := by
  intro w
  induction r generalizing w with
  | empty => exact regex_to_nfa_correct_empty w
  | epsilon => exact regex_to_nfa_correct_epsilon w
  | char a => exact regex_to_nfa_correct_char a w
  | alt r1 r2 ih1 ih2 => exact regex_to_nfa_correct_alt r1 r2 w (ih1 w) (ih2 w)
  | seq r1 r2 ih1 ih2 => exact regex_to_nfa_correct_seq r1 r2 w ih1 ih2
  | star r ih => exact regex_to_nfa_correct_star r w ih

-- NFAから正規表現への変換（状態除去法など）
def nfa_to_regex [DecidableEq σ] (nfa : NFA σ) : Regex σ := by
  sorry

-- 変換の正しさ
theorem nfa_to_regex_correct [DecidableEq σ] (nfa : NFA σ) :
  ∀ w : List σ, (nfa accepts w) ↔ ((nfa_to_regex nfa) ~ w) := by
  sorry

-- =========================================
-- 正規表現とNFAの等価性
-- =========================================

-- 存在定理：正規表現からNFAへの変換が存在する
theorem regex_to_nfa_exists [DecidableEq σ] (r : Regex σ) :
  ∃ (nfa : NFA σ), ∀ w : List σ, (r ~ w) ↔ (nfa accepts w) := by
  use regex_to_nfa r
  exact regex_to_nfa_correct r

-- 存在定理：NFAから正規表現への変換が存在する
theorem nfa_to_regex_exists [DecidableEq σ] (nfa : NFA σ) :
  ∃ (r : Regex σ), ∀ w : List σ, (nfa accepts w) ↔ (r ~ w) := by
  use nfa_to_regex nfa
  exact nfa_to_regex_correct nfa


-- =========================================
-- 補助定理・補題（必要に応じて追加）
-- =========================================
