# unfoldタクティック - 定義を展開する

## 概要

`unfold`は関数や定義を展開（unfold）して、その実装の詳細を見えるようにするタクティック。証明の中で抽象的な定義を具体的な形に展開することで、証明を進めやすくする。

## 基本的な使い方

### 構文

```lean
unfold 定義名1 定義名2 ...        -- ゴールの中で展開
unfold 定義名1 定義名2 ... at h  -- 仮定hの中で展開
```

### 実際の例

#### 例1: ゴールの中で展開

```lean
-- 定義
def NFA.Accepts (nfa : NFA σ) (w : List σ) : Prop :=
  ∃ qf, qf ∈ nfa.F ∧ Run nfa nfa.q₀ w qf

-- 証明の中で
theorem example1 : NFA.epsilon accepts [] := by
  unfold NFA.Accepts
  -- ゴールが以下に変わる：
  -- ∃ qf, qf ∈ NFA.epsilon.F ∧ Run NFA.epsilon NFA.epsilon.q₀ [] qf
  use 1
  ...
```

**展開前のゴール:**
```
⊢ NFA.epsilon accepts []
```

**展開後のゴール:**
```
⊢ ∃ qf, qf ∈ NFA.epsilon.F ∧ Run NFA.epsilon NFA.epsilon.q₀ [] qf
```

#### 例2: 仮定の中で展開

```lean
theorem example2 (h : NFA.epsilon accepts w) : ... := by
  unfold NFA.Accepts at h
  -- h の型が以下に変わる：
  -- h : ∃ qf, qf ∈ NFA.epsilon.F ∧ Run NFA.epsilon NFA.epsilon.q₀ w qf
  obtain ⟨qf, hqf_in_F, hrun⟩ := h
  ...
```

**展開前の仮定:**
```
h : NFA.epsilon accepts w
```

**展開後の仮定:**
```
h : ∃ qf, qf ∈ NFA.epsilon.F ∧ Run NFA.epsilon NFA.epsilon.q₀ w qf
```

## プロジェクトでの使用例

### 例: regex_to_nfa_correctの証明

```lean
theorem regex_to_nfa_correct_epsilon (w : List σ) :
  (Regex.epsilon ~ w) ↔ (regex_to_nfa Regex.epsilon accepts w) := by
  constructor
  · intro h
    cases h
    -- ここでunfoldを使用
    unfold regex_to_nfa NFA.Accepts
    -- 2つの定義を同時に展開：
    -- regex_to_nfa Regex.epsilon → NFA.epsilon
    -- NFA.Accepts → ∃ qf, qf ∈ nfa.F ∧ Run ...
    use 1
    constructor
    · simp [NFA.epsilon]
    · ...
```

### 展開される様子

1. **元のゴール:**
   ```
   ⊢ regex_to_nfa Regex.epsilon accepts []
   ```

2. **`unfold regex_to_nfa`後:**
   ```
   ⊢ NFA.epsilon accepts []
   ```

3. **`unfold NFA.Accepts`後:**
   ```
   ⊢ ∃ qf, qf ∈ NFA.epsilon.F ∧ Run NFA.epsilon NFA.epsilon.q₀ [] qf
   ```

## unfoldとsimpの違い

| タクティック | 役割 | いつ使うか |
|------------|------|-----------|
| **unfold** | 指定した定義を1回だけ展開 | 特定の定義を明示的に展開したいとき |
| **simp** | 既知の等式を使って自動的に簡約 | 定義を展開しつつ簡約もしたいとき |

### 例で比較

```lean
def double (n : Nat) := n + n
def quadruple (n : Nat) := double (double n)

example : quadruple 2 = 8 := by
  -- unfoldは1段階ずつ展開
  unfold quadruple
  -- ゴール: double (double 2) = 8
  unfold double
  -- ゴール: (double 2) + (double 2) = 8
  unfold double
  -- ゴール: (2 + 2) + (2 + 2) = 8
  rfl

example : quadruple 2 = 8 := by
  -- simpは自動的に全部やってくれる
  simp [quadruple, double]
  -- 即座に証明完了
```

## いつunfoldを使うべきか

### ✅ unfoldが便利な場合

1. **証明の流れを明確にしたいとき**
   ```lean
   unfold NFA.Accepts
   -- 「この定義を展開して、存在証明の形にする」という意図が明確
   ```

2. **部分的に展開したいとき**
   ```lean
   unfold regex_to_nfa
   -- NFA.Acceptsはまだ展開しない
   ```

3. **証明を読みやすくしたいとき**
   - `simp`は何をしているか分かりにくい
   - `unfold`は「この定義を見せる」という意図が明確

### ❌ unfoldが不要な場合

1. **simpで済む場合**
   ```lean
   -- ❌ 冗長
   unfold foo; unfold bar; unfold baz; simp

   -- ✅ 簡潔
   simp [foo, bar, baz]
   ```

2. **定義が複雑すぎる場合**
   - 展開するとゴールが読めなくなる
   - 補題を使う方が良い

## 高度な使い方

### 複数の定義を同時に展開

```lean
unfold regex_to_nfa NFA.Accepts NFA.Run
-- 3つの定義を一度に展開
```

### 特定の場所だけ展開

```lean
-- 仮定h1とh2の中だけで展開
unfold NFA.Accepts at h1 h2
```

### すべての場所で展開

```lean
-- ゴールと全ての仮定で展開
unfold NFA.Accepts at *
```

## よくあるエラー

### エラー1: 展開できない定義

```lean
-- ❌ エラー
theorem foo : 1 + 1 = 2 := by
  unfold Nat.add  -- Nat.addは組み込み定義なので展開できない
```

**解決策**: `simp`や`rfl`を使う

### エラー2: 展開しすぎて複雑になる

```lean
-- ❌ ゴールが長すぎて読めない
unfold big_complicated_definition
-- ゴール: (λ x => (λ y => (λ z => ...)))(foo)(bar)(baz) = ...
```

**解決策**: 補題を作って段階的に証明する

## まとめ

| 項目 | 説明 |
|------|------|
| **目的** | 定義を展開して具体的な形にする |
| **基本構文** | `unfold 定義名` または `unfold 定義名 at h` |
| **利点** | 証明の意図が明確、段階的な展開が可能 |
| **欠点** | simpより冗長になることがある |
| **使い分け** | 明示的に見せたいとき→unfold、自動で良いとき→simp |

## 関連タクティック

- **simp**: 定義展開+簡約を自動で行う
- **dsimp**: 定義的等価性のみで簡約（証明項を変えない）
- **rw**: 等式で書き換える
- **show**: ゴールを明示的に書き換える（定義的に等しい形に）
