import RegexNFA.NFA
import RegexNFA.Regex

-- =========================================
-- 正規表現とNFAの等価性
-- =========================================

-- 存在定理：正規表現からNFAへの変換が存在する
theorem regex_to_nfa_exists (r : Regex σ) :
  ∃ (nfa : NFA σ), ∀ w : List σ, (r ~ w) ↔ (nfa accepts w) := by
  sorry

-- 存在定理：NFAから正規表現への変換が存在する
theorem nfa_to_regex_exists (nfa : NFA σ) :
  ∃ (r : Regex σ), ∀ w : List σ, (nfa accepts w) ↔ (r ~ w) := by
  sorry

-- =========================================
-- 構成的な変換関数（Thompson構成法など）
-- =========================================

-- 正規表現からNFAへの変換（Thompson構成法）
def regex_to_nfa (r : Regex σ) : NFA σ := by
  sorry

-- 変換の正しさ
theorem regex_to_nfa_correct (r : Regex σ) :
  ∀ w : List σ, (r ~ w) ↔ ((regex_to_nfa r) accepts w) := by
  sorry

-- NFAから正規表現への変換（状態除去法など）
def nfa_to_regex (nfa : NFA σ) : Regex σ := by
  sorry

-- 変換の正しさ
theorem nfa_to_regex_correct (nfa : NFA σ) :
  ∀ w : List σ, (nfa accepts w) ↔ ((nfa_to_regex nfa) ~ w) := by
  sorry

-- =========================================
-- 補助定理・補題（必要に応じて追加）
-- =========================================
