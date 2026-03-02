# casesタクティック - 帰納的な型の場合分け

## 核心となる理解

**`cases`は帰納的な型（inductive type）の値に対して、「どのコンストラクタで作られたか」で場合分けするタクティック**

## 基本的な仕組み

```lean
h : InductiveType
cases h
-- → hがどのコンストラクタで構築されたかで場合分け
-- → コンストラクタが n 個あれば、n 個のケースに分かれる
```

## コンストラクタの数による違い

### ケース1: コンストラクタが0個 → 矛盾から証明完了

```lean
-- Regex.Matchesの定義
inductive Regex.Matches : Regex σ → List σ → Prop where
  -- empty: 何も受理しない（コンストラクタなし）← 0個！
  | epsilon : Matches epsilon []
  | char : Matches (char a) [a]
  ...

-- 証明で
h : Regex.empty ~ w
cases h
-- Regex.emptyに対応するコンストラクタは0個
-- → 場合分けするケースが0個
-- → すべてのケース（ゼロ個）を処理した
-- → 証明完了！
```

### ケース2: コンストラクタが1個 → 情報を学習

```lean
-- epsilonコンストラクタは1つだけ
| epsilon : Matches epsilon []

-- 証明で
h : Regex.epsilon ~ w
cases h
-- epsilonコンストラクタのケースのみ:
-- このコンストラクタは Matches epsilon [] を作る
-- → w = [] でなければならない
-- → w が [] に置き換わる
```

もう一つの例：

```lean
h : Regex.char a ~ w
cases h
-- charコンストラクタのケースのみ:
-- このコンストラクタは Matches (char a) [a] を作る
-- → w = [a] でなければならない
-- → w が [a] に置き換わる
```

### ケース3: コンストラクタが2個以上 → 複数のケースに分岐

```lean
-- altには2つのコンストラクタがある
| altLeft : Matches r1 w → Matches (alt r1 r2) w
| altRight : Matches r2 w → Matches (alt r1 r2) w

-- 証明で
h : Regex.alt r1 r2 ~ w
cases h with
| altLeft h1 =>
  -- r1 ~ w のケース
  -- h1 : r1 ~ w を使って証明
  sorry
| altRight h2 =>
  -- r2 ~ w のケース
  -- h2 : r2 ~ w を使って証明
  sorry
```

## 標準的な例

### Bool型
```lean
inductive Bool where
  | true   -- コンストラクタ1
  | false  -- コンストラクタ2

example (b : Bool) : ... := by
  cases b with
  | true =>
    -- b = true のケース
    sorry
  | false =>
    -- b = false のケース
    sorry
```

### Option型
```lean
inductive Option (α : Type) where
  | none       -- コンストラクタ1
  | some (a : α)  -- コンストラクタ2

example (opt : Option Nat) : ... := by
  cases opt with
  | none =>
    -- opt = none のケース
    sorry
  | some n =>
    -- opt = some n のケース
    -- n : Nat が手に入る
    sorry
```

### List型
```lean
inductive List (α : Type) where
  | nil         -- コンストラクタ1: 空リスト
  | cons (head : α) (tail : List α)  -- コンストラクタ2: 要素追加

example (lst : List Nat) : ... := by
  cases lst with
  | nil =>
    -- lst = [] のケース
    sorry
  | cons head tail =>
    -- lst = head :: tail のケース
    -- head : Nat, tail : List Nat が手に入る
    sorry
```

## プロジェクトでの使用例

### 例1: empty（コンストラクタ0個）

```lean
theorem regex_to_nfa_correct_empty (w : List σ) :
  (Regex.empty ~ w) ↔ ... := by
  constructor
  · intro h
    cases h  -- ← コンストラクタ0個 → 証明完了！
  · ...
```

### 例2: epsilon（コンストラクタ1個）

```lean
theorem regex_to_nfa_correct_epsilon (w : List σ) :
  (Regex.epsilon ~ w) ↔ ... := by
  constructor
  · intro h
    cases h  -- ← w = [] を学習
    -- この時点で w = []
    unfold regex_to_nfa NFA.Accepts
    use 1
    ...
```

### 例3: alt（コンストラクタ2個）

```lean
-- 将来的な実装
theorem regex_to_nfa_correct_alt (r1 r2 : Regex σ) :
  ∀ w, (Regex.alt r1 r2 ~ w) ↔ ... := by
  intro w
  constructor
  · intro h
    cases h with  -- ← 2つのケースに分岐
    | altLeft h1 =>
      -- r1 ~ w のケース
      sorry
    | altRight h2 =>
      -- r2 ~ w のケース
      sorry
```

## casesとinductionの違い

| タクティック | 用途 | いつ使うか |
|------------|------|-----------|
| **cases** | 場合分け（帰納法の仮定なし） | 値の構造を分析するだけでよい時 |
| **induction** | 場合分け + 帰納法の仮定 | 再帰的な構造で証明する時 |

### 例：Natに対して

```lean
-- casesの場合
n : Nat
cases n with
| zero => -- n = 0 のケース
| succ n' => -- n = n' + 1 のケース
  -- n' : Nat が手に入る（帰納法の仮定なし）

-- inductionの場合
n : Nat
induction n with
| zero => -- n = 0 のケース
| succ n' ih => -- n = n' + 1 のケース
  -- n' : Nat が手に入る
  -- ih : (ゴールのn'版) も手に入る（帰納法の仮定）
```

## コンストラクタ数と証明への影響

| コンストラクタ数 | `cases`の効果 | 例 |
|----------------|--------------|-----|
| **0個** | 即座に証明完了（矛盾） | `Regex.empty`, `False`, `Empty` |
| **1個** | 情報を学習・パラメータ抽出 | `Regex.epsilon`, `Regex.char` |
| **2個** | 2つのケースに分岐 | `Bool`, `Option`, `Regex.alt` |
| **n個** | n個のケースに分岐 | `Regex` (6個), `Nat` (2個) |

## まとめ

### 核心
**`cases`は帰納的な型の値を「どのコンストラクタで作られたか」で場合分けする**

### 覚えておくべきパターン

1. **コンストラクタ0個** → 矛盾 → 証明完了
   ```lean
   cases h  -- h : Regex.empty ~ w
   -- 即座に完了
   ```

2. **コンストラクタ1個** → 情報学習
   ```lean
   cases h  -- h : Regex.epsilon ~ w
   -- w = [] が判明
   ```

3. **コンストラクタ複数** → 場合分け
   ```lean
   cases h with
   | constructor1 => ...
   | constructor2 => ...
   ```

### 関連タクティック
- **induction**: 帰納法（帰納法の仮定も得られる）
- **match**: パターンマッチ（証明ではなく定義で使う）
- **rcases**: 複数レベルの分解を一度に行う
