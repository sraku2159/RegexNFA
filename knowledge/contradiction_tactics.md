# 矛盾を扱うタクティック

## 概要

Leanで矛盾（False）から証明を完了させる方法はいくつかある。「矛盾からは何でも導ける」（ex falso quodlibet）という論理原理を使う。

## 使用例：NFA.empty

```lean
theorem regex_to_nfa_correct_empty (w : List σ) :
  (Regex.empty ~ w) ↔ (regex_to_nfa Regex.empty accepts w) := by
  constructor
  · intro h; cases h  -- Regex.emptyにはコンストラクタがない
  · intro h
    unfold regex_to_nfa NFA.Accepts at h
    obtain ⟨qf, hqf_in_F, _⟩ := h
    -- hqf_in_F : qf ∈ NFA.empty.F
    simp [NFA.empty] at hqf_in_F
    -- hqf_in_F : qf ∈ ∅ → これは矛盾（False）

    -- ここから矛盾を使って証明完了させる方法がいくつかある
```

## 方法1: `contradiction`（推奨）

```lean
simp [NFA.empty] at hqf_in_F
contradiction
```

### 特徴
- **自動的に矛盾を検出**: コンテキスト内の矛盾を自動で見つけて証明完了
- **最も簡潔**: 1行で済む
- **意図が明確**: 「矛盾がある」という意図が名前から分かる

### いつ使うか
- コンテキストに明らかな矛盾がある時
- 最も推奨される方法

## 方法2: `cases`

```lean
simp [NFA.empty] at hqf_in_F
cases hqf_in_F
```

### 特徴
- **ケース分解**: Falseのコンストラクタで場合分け → コンストラクタが0個なので即座に完了
- **一貫性**: empty型の証明と同じパターン

### 説明
```lean
-- hqf_in_F : False (または qf ∈ ∅)
cases hqf_in_F
-- Falseには何もコンストラクタがないので、
-- 場合分けするケースが0個
-- → すべてのケースを処理した → 証明完了
```

### いつ使うか
- Falseや空集合のメンバーシップなど、明らかに構築不可能な型の値がある時
- empty型の扱いと同じパターンで統一したい時

## 方法3: `exfalso`

```lean
simp [NFA.empty] at hqf_in_F
exfalso
exact hqf_in_F
```

### 特徴
- **明示的**: ゴールを`False`に変更してから証明
- **教育的**: 何が起きているか非常に明確

### ステップバイステップ
```lean
-- 元のゴール: Regex.empty ~ w

simp [NFA.empty] at hqf_in_F
-- hqf_in_F : False

exfalso
-- ゴールが False に変わる
-- ⊢ False

exact hqf_in_F
-- hqf_in_F : False を使って証明
```

### いつ使うか
- 証明の流れを明示的に示したい時
- 「矛盾からFalseを導き、Falseから任意のゴールを導く」という流れを見せたい時

## 方法4: 何もしない

```lean
simp [NFA.empty] at hqf_in_F
-- 場合によっては自動で完了
```

### 特徴
- **最も簡潔**: タクティックすら不要
- **不確実**: 動作しないこともある

### いつ動くか
- `simp`が矛盾を検出して自動的に証明を完了させた場合
- ただし、確実ではないので推奨されない

## 方法5: `absurd`

```lean
simp [NFA.empty] at hqf_in_F
absurd hqf_in_F (by simp)
```

### 特徴
- **古典的**: `P ∧ ¬P`のような矛盾を扱う
- **やや複雑**: 引数が2つ必要

### 構文
```lean
absurd (proof_of_P) (proof_of_not_P)
```

### いつ使うか
- `P`と`¬P`の両方が明示的にある時
- あまり使わない

## 比較表

| タクティック | 簡潔さ | 明確さ | 自動化 | 推奨度 |
|------------|--------|--------|--------|--------|
| `contradiction` | ★★★ | ★★☆ | ★★★ | ★★★ |
| `cases` | ★★★ | ★★★ | ★☆☆ | ★★☆ |
| `exfalso; exact h` | ★☆☆ | ★★★ | ★☆☆ | ★★☆ |
| 何もしない | ★★★ | ★☆☆ | ★★☆ | ★☆☆ |
| `absurd` | ★☆☆ | ★★☆ | ★☆☆ | ★☆☆ |

## `simp` vs `rw` で矛盾を導く

### `simp`を使う場合
```lean
simp [NFA.empty] at hqf_in_F
-- NFA.emptyの定義を展開して簡約
-- hqf_in_F : False (または qf ∈ ∅ → False と簡約される)
contradiction
```

### `rw`を使う場合
```lean
rw [NFA.empty] at hqf_in_F
-- NFA.emptyの定義で書き換え
-- hqf_in_F : qf ∈ ∅
contradiction
-- contradictionがqf ∈ ∅をFalseとして認識
```

### 違い
- **`simp`**: 定義展開 + 簡約を自動で行う
- **`rw`**: 定義展開のみ（簡約は手動）

どちらでも動作するが、`simp`の方が自動化されている。

## 実際のプロジェクトでの使用例

```lean
theorem regex_to_nfa_correct_empty [DecidableEq σ] (w : List σ) :
  (Regex.empty ~ w) ↔ (regex_to_nfa Regex.empty accepts w) := by
  constructor
  · intro h
    cases h  -- 方法2: Regex.emptyにコンストラクタなし
  · intro h
    unfold regex_to_nfa NFA.Accepts at h
    obtain ⟨qf, hqf_in_F, _⟩ := h
    simp [NFA.empty] at hqf_in_F
    contradiction  -- 方法1: 自動で矛盾検出
```

## 推奨される使い分け

1. **通常**: `contradiction`を使う（簡潔で自動）
2. **教育的に明示したい**: `exfalso; exact h`を使う
3. **empty型と統一**: `cases h`を使う
4. **高度な場合**: `absurd`を使う（稀）

## まとめ

| 状況 | 推奨タクティック |
|------|-----------------|
| 一般的な矛盾 | `contradiction` |
| 空の型・False | `cases h` |
| 明示的な説明 | `exfalso; exact h` |
| ¬P ∧ P の形 | `absurd` |

**基本**: `contradiction`を使えば大抵うまくいく！
