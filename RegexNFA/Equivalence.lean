import RegexNFA.NFA
import RegexNFA.Regex

-- =========================================
-- 構成的な変換関数（Thompson構成法など）
-- =========================================

-- 正規表現からNFAへの変換（Thompson構成法）
def regex_to_nfa [DecidableEq σ] (r : Regex σ) : SomeNFA σ :=
  match r with
  | .empty => ⟨Fin 1, inferInstance, NFA.empty σ⟩
  | .epsilon => ⟨Fin 2, inferInstance, NFA.epsilon σ⟩
  | .char a => ⟨Fin 2, inferInstance, NFA.char σ a⟩
  | .alt r1 r2 =>
      let ⟨S1, inst1, nfa1⟩ := regex_to_nfa r1
      let ⟨S2, inst2, nfa2⟩ := regex_to_nfa r2
      ⟨AltState S1 S2, inferInstance, @NFA.alt σ S1 S2 _ inst1 inst2 nfa1 nfa2⟩
  | .seq r1 r2 =>
      let ⟨S1, inst1, nfa1⟩ := regex_to_nfa r1
      let ⟨S2, inst2, nfa2⟩ := regex_to_nfa r2
      ⟨SeqState S1 S2, inferInstance, @NFA.seq σ S1 S2 _ inst1 inst2 nfa1 nfa2⟩
  | .star r =>
      let ⟨S, inst, nfa⟩ := regex_to_nfa r
      ⟨StarState S, inferInstance, @NFA.star σ S _ inst nfa⟩

-- =========================================
-- 各ケースの補題
-- =========================================

-- 証明は後で完成させる
theorem regex_to_nfa_correct_empty [DecidableEq σ] (w : List σ) :
  (Regex.empty ~ w) ↔ (regex_to_nfa Regex.empty accepts w) := by
  sorry

theorem regex_to_nfa_correct_epsilon [DecidableEq σ] (w : List σ) :
  (Regex.epsilon ~ w) ↔ (regex_to_nfa Regex.epsilon accepts w) := by
  sorry

theorem regex_to_nfa_correct_char [DecidableEq σ] (a : σ) (w : List σ) :
  (Regex.char a ~ w) ↔ (regex_to_nfa (Regex.char a) accepts w) := by
  sorry

theorem regex_to_nfa_correct_alt [DecidableEq σ] (r1 r2 : Regex σ) (w : List σ)
  (ih1 : (r1 ~ w) ↔ (regex_to_nfa r1 accepts w))
  (ih2 : (r2 ~ w) ↔ (regex_to_nfa r2 accepts w)) :
  (Regex.alt r1 r2 ~ w) ↔ (regex_to_nfa (Regex.alt r1 r2) accepts w) := by
  sorry

theorem regex_to_nfa_correct_seq [DecidableEq σ] (r1 r2 : Regex σ) (w : List σ)
  (ih1 : ∀ w1, (r1 ~ w1) ↔ (regex_to_nfa r1 accepts w1))
  (ih2 : ∀ w2, (r2 ~ w2) ↔ (regex_to_nfa r2 accepts w2)) :
  (Regex.seq r1 r2 ~ w) ↔ (regex_to_nfa (Regex.seq r1 r2) accepts w) := by
  sorry

theorem regex_to_nfa_correct_star [DecidableEq σ] (r : Regex σ) (w : List σ)
  (ih : ∀ w', (r ~ w') ↔ (regex_to_nfa r accepts w')) :
  (Regex.star r ~ w) ↔ (regex_to_nfa (Regex.star r) accepts w) := by
  sorry

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
def nfa_to_regex [DecidableEq σ] (snfa : SomeNFA σ) : Regex σ := by
  sorry

-- 変換の正しさ
theorem nfa_to_regex_correct [DecidableEq σ] (snfa : SomeNFA σ) :
  ∀ w : List σ, (snfa accepts w) ↔ ((nfa_to_regex snfa) ~ w) := by
  sorry

-- =========================================
-- 正規表現とNFAの等価性
-- =========================================

-- 存在定理：正規表現からNFAへの変換が存在する
theorem regex_to_nfa_exists [DecidableEq σ] (r : Regex σ) :
  ∃ (snfa : SomeNFA σ), ∀ w : List σ, (r ~ w) ↔ (snfa accepts w) := by
  use regex_to_nfa r
  exact regex_to_nfa_correct r

-- 存在定理：NFAから正規表現への変換が存在する
theorem nfa_to_regex_exists [DecidableEq σ] (snfa : SomeNFA σ) :
  ∃ (r : Regex σ), ∀ w : List σ, (snfa accepts w) ↔ (r ~ w) := by
  use nfa_to_regex snfa
  exact nfa_to_regex_correct snfa


-- =========================================
-- 補助定理・補題（必要に応じて追加）
-- =========================================
