# 空の型による証明（Empty Type Proofs）

## 概要

Leanでは、コンストラクタが存在しない帰納型（empty type）を使うことで、「不可能なケース」を表現できる。このような型の値を仮定すると、`cases`タクティックだけで証明が完了する。

## 具体例：Regex.empty

### 定義

```lean
inductive Regex.Matches : Regex σ → List σ → Prop where
  -- empty: 何も受理しない（コンストラクタなし）
  | epsilon : Matches epsilon []
  | char : Matches (char a) [a]
  | altLeft : Matches r1 w → Matches (alt r1 r2) w
  ...
```

**重要**: `Regex.empty`に対応するコンストラクタが**存在しない**！

### 証明

```lean
theorem regex_to_nfa_correct_empty (w : List σ) :
  (Regex.empty ~ w) ↔ (regex_to_nfa Regex.empty accepts w) := by
  constructor
  · intro h
    cases h  -- ← これだけで証明完了！
  · intro h
    -- （後半の証明）
    ...
```

### なぜ`cases h`だけで証明が完了するのか？

1. **`h : Regex.empty ~ w`** という仮定がある
2. **`cases h`** は「hがどのコンストラクタで構築されたか」を場合分けする
3. しかし`Regex.empty`に対応するコンストラクタは**0個**
4. 場合分けすべきケースが**0個**なので、すべてのケースを処理した → 証明完了！

これは**矛盾からは何でも証明できる**（ex falso quodlibet）という論理の原理。

## 一般的なパターン

### 標準ライブラリの例

```lean
-- Emptyは標準ライブラリで定義されている空の型
inductive Empty : Type
  -- コンストラクタなし

-- Emptyから任意の命題を証明できる
theorem absurd_from_empty {P : Prop} (h : Empty) : P := by
  cases h  -- 即座に完了
```

### Falseも同様

```lean
-- Falseも実はコンストラクタがない帰納型
inductive False : Prop
  -- コンストラクタなし

theorem false_elim {P : Prop} (h : False) : P := by
  cases h
```

## 設計上の利点

### 「何も受理しない」を型レベルで表現

- **明示的なケース分けが不要**: コンストラクタがないので、自然に「存在しない」ことが保証される
- **型安全**: 間違えて`Regex.empty ~ w`の証明を作ってしまうことが不可能
- **証明が簡潔**: `cases h`一発で矛盾を導出できる

### 他の選択肢との比較

もし`empty`をコンストラクタとして定義していたら：

```lean
-- ❌ こうしていたら
inductive Regex.Matches : Regex σ → List σ → Prop where
  | empty_never : ∀ w, ¬Matches empty w  -- ← これは冗長
  | epsilon : Matches epsilon []
  ...

-- 証明がもっと複雑になる
theorem proof (h : Regex.empty ~ w) : False := by
  cases h with
  | empty_never w' hnot =>
    apply hnot
    -- ここで循環してしまう...
```

現在の設計（コンストラクタなし）の方がはるかに簡潔！

## まとめ

| 概念 | 説明 | 例 |
|------|------|-----|
| **Empty type** | コンストラクタが0個の帰納型 | `Empty`, `False` |
| **使い方** | 不可能なケース・矛盾を表現 | `Regex.empty` に対応するコンストラクタなし |
| **証明方法** | `cases h` で即座に完了 | `intro h; cases h` |
| **原理** | Ex falso quodlibet（矛盾からは何でも導ける） | 空の場合分けは自動的に完了 |

## 関連する概念

- **Inhabited vs Empty**: `Inhabited α`は「αの値が少なくとも1つ存在する」、Empty typeは「値が存在しない」
- **Option型との違い**: `Option.none`は値が存在する（noneというコンストラクタ）が、Empty typeは値自体が存在しない
- **Void型**: Haskellの`Void`や他の言語の似た概念と同じアイデア
