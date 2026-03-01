# Leanの終了性：defとinductiveの違い

## 概要

Leanでは、すべての関数が**有限時間で終了する（terminate）**ことを保証する必要があります。これは型理論の健全性を保つために必須の要件です。

この文書では、`def`（関数定義）で終了性エラーが発生する理由と、`inductive`（帰納的述語）を使うことでその問題を回避できる理由を説明します。

## 発生した問題

正規表現のマッチング関数を`def`で定義しようとしたところ、以下のエラーが発生しました：

```
fail to show termination for
  Regex.matches
with errors
failed to infer structural recursion:
Cannot use parameter #3:
  failed to eliminate recursive application
    r1.matches w
```

## `def`（関数定義）の場合

### 関数定義とは

`def`は**計算手続き**を定義します。関数を呼び出すと、定義に従って値が計算されます。

```lean
def Regex.matches : Regex σ → List σ → Prop
  | empty, _ => False
  | epsilon, w => w = []
  | char a, w => w = [a]
  | alt r1 r2, w => r1.matches w ∨ r2.matches w
  | seq r1 r2, w => ∃ w1 w2, w = w1 ++ w2 ∧ r1.matches w1 ∧ r2.matches w2
  | star r, [] => True
  | star r, w => ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ r.matches w1 ∧ (star r).matches w2
```

### なぜ終了性チェックが必要か

もし終了性チェックがなければ、以下のような無限ループ関数が定義できてしまいます：

```lean
-- これが許されると矛盾が導ける
def loop : Nat → Nat
  | n => loop n  -- 永遠に終わらない！
```

これを使うと、型理論の健全性が崩れ、`False`（矛盾）を証明できてしまいます。

### `star`のケースでの問題

```lean
| star r, w => ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ r.matches w1 ∧ (star r).matches w2
                                                                 ^^^^^^^^^^^^^^^^
                                                                 再帰呼び出し
```

**人間の視点では：**
- `w = w1 ++ w2` かつ `w1 ≠ []` なので、`w2.length < w.length`
- 文字列の長さが減っていくので、必ず終了する

**Leanの視点では：**
- `star r` → `star r`（正規表現の構造は同じ！）
- `w` → `w2`（文字列が減っているが、`∃`の中にあるため自動推論できない）
- 何が減っているのか明示的に証明する必要がある

### なぜLeanは自動推論できないか

Leanは構造的再帰を優先的に探します：

1. **パラメータ1（正規表現）**: `star r` → `star r` で変化なし ❌
2. **パラメータ2（文字列）**: `w` → `w2` だが、`∃`の中で束縛されているため、Leanが自動的に`w2 < w`を推論できない ❌

`termination_by`を使えば明示的に証明できますが、`seq`や`star`のケースで複雑な証明が必要になります。

## `inductive`（帰納的述語）の場合

### 帰納的述語とは

`inductive`は**証明のルール**を定義します。計算手続きではなく、「どういう条件で関係が成り立つか」を宣言します。

```lean
inductive Regex.Matches : Regex σ → List σ → Prop where
  | epsilon : Matches epsilon []
  | char : Matches (char a) [a]
  | altLeft : Matches r1 w → Matches (alt r1 r2) w
  | altRight : Matches r2 w → Matches (alt r1 r2) w
  | seq : Matches r1 w1 → Matches r2 w2 → Matches (seq r1 r2) (w1 ++ w2)
  | starEmpty : Matches (star r) []
  | starConcat : w1 ≠ [] → Matches r w1 → Matches (star r) w2 →
                 Matches (star r) (w1 ++ w2)
```

### なぜ終了性チェックが不要か

**重要な違い：**
- `def`は**計算する**ため、無限ループの可能性がある
- `inductive`は**証明木を構築する**だけで、計算しない

```lean
-- inductive の使い方：証明を構築する
example : Matches (star (char 'a')) ['a', 'a'] := by
  apply starConcat
  · -- w1 ≠ [] の証明
    simp
  · -- Matches (char 'a') ['a'] の証明
    apply char
  · -- Matches (star (char 'a')) ['a'] の証明
    apply starConcat
    · simp
    · apply char
    · apply starEmpty
```

各`apply`は新しい証明ノードを追加するだけで、計算処理は行いません。証明木の構造が有限であることは、Leanの型システムが保証します。

## 具体例での比較

### `def`版（エラーになる）

```lean
def Regex.matches : Regex σ → List σ → Prop
  | star r, w => ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧
                 r.matches w1 ∧ (star r).matches w2
--                                ^^^^^^^^^^^^^^^^
--                                終了性エラー！

-- 使い方：
#check (star (char 'a')).matches ['a', 'a']
-- → Leanが定義を展開して計算を試みる
-- → 再帰呼び出しが終了するか検証できない
```

### `inductive`版（エラーなし）

```lean
inductive Regex.Matches : Regex σ → List σ → Prop where
  | starConcat : w1 ≠ [] → Matches r w1 → Matches (star r) w2 →
                 Matches (star r) (w1 ++ w2)
--                                  ^^^^^^
--                                  問題なし！

-- 使い方：
example : Matches (star (char 'a')) ['a', 'a'] := by
  apply starConcat  -- 証明ルールを適用するだけ
  ...
```

## 比喩的説明

### `def`（関数）はレシピ

```
料理の作り方（計算手続き）:
1. 材料を切る
2. 鍋に入れる
3. 味見する
4. まずかったら1に戻る ← これが永遠に続いたら？
```

→ Leanは「このレシピは必ず完成する？」と心配する（終了性チェック）

### `inductive`（述語）はルール集

```
「美味しい」という性質の定義（証明ルール）:
- ルール1: 甘いものは美味しい
- ルール2: 美味しいものに塩を少し足しても美味しい
- ルール3: 美味しいもの同士を混ぜると美味しい
```

→ ルールを適用するだけ。計算しないので、終了性の心配なし

## 比較表

| | `def` (関数) | `inductive` (述語) |
|---|---|---|
| **何を定義？** | 計算手続き | 証明ルール／関係 |
| **実行すると？** | 値を計算する | 証明を構築する |
| **再帰の扱い** | 終了性証明が必要 | 終了性不要 |
| **使い方** | `r.matches w` | `Matches r w` |
| **パターンマッチ** | 関数のパターンマッチ | コンストラクタで表現 |
| **エラー** | 終了性が証明できないとエラー | 構造が正しければOK |
| **証明の書きやすさ** | 関数の性質を証明 | 帰納法が自然に使える |

## 実践例：RegexNFA実装での適用

### 問題の発生

```lean
def Regex.matches : Regex σ → List σ → Prop
  | star r, w => ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ r.matches w1 ∧ (star r).matches w2
```

エラー：
```
failed to infer structural recursion:
Cannot use parameter #3:
  failed to eliminate recursive application
    r1.matches w
```

### 解決策

`inductive`で書き直す：

```lean
inductive Regex.Matches : Regex σ → List σ → Prop where
  | epsilon : Matches epsilon []
  | char : Matches (char a) [a]
  | altLeft : Matches r1 w → Matches (alt r1 r2) w
  | altRight : Matches r2 w → Matches (alt r1 r2) w
  | seq : Matches r1 w1 → Matches r2 w2 → Matches (seq r1 r2) (w1 ++ w2)
  | starEmpty : Matches (star r) []
  | starConcat : w1 ≠ [] → Matches r w1 → Matches (star r) w2 →
                 Matches (star r) (w1 ++ w2)
```

### 利点

1. **終了性エラーが消える** - 計算しないので終了性不要
2. **証明が書きやすい** - 帰納法による証明が自然
3. **理論的に綺麗** - 形式言語理論の標準的な定義に近い

## 参考：その他の解決策

### 案1: `termination_by`を使う

```lean
def Regex.matches : Regex σ → List σ → Prop
  | empty, _ => False
  | epsilon, w => w = []
  | char a, w => w = [a]
  | alt r1 r2, w => r1.matches w ∨ r2.matches w
  | seq r1 r2, w => ∃ w1 w2, w = w1 ++ w2 ∧ r1.matches w1 ∧ r2.matches w2
  | star r, [] => True
  | star r, w => ∃ w1 w2, w1 ≠ [] ∧ w = w1 ++ w2 ∧ r.matches w1 ∧ (star r).matches w2
termination_by _ w => w.length
decreasing_by
  all_goals sorry  -- 各ケースで文字列の長さが減ることを証明（複雑）
```

**欠点:**
- `decreasing_by`で各再帰呼び出しについて、長さが減ることを証明する必要がある
- `seq`や`star`のケースで、`∃`の中の変数について証明が複雑

### 案2: 補助関数を分ける

計算部分と論理部分を分離する方法もありますが、この問題では`inductive`が最もシンプルです。

## まとめ

- **`def`は計算手続き** → 終了性証明が必要
- **`inductive`は証明ルール** → 終了性不要
- **再帰的な関係を定義するときは`inductive`が適している**
- 今回のような形式言語の定義では、`inductive`が理論的にも実装上も最適

## 関連リンク

- [Lean公式ドキュメント: Inductive Types](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html)
- [Lean公式ドキュメント: Recursion and Termination](https://lean-lang.org/functional_programming_in_lean/programs-proofs/tail-recursion.html)
