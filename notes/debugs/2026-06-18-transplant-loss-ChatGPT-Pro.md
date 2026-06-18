# 結論

**ある。かなりめざとく拾うと、実質7系統・症状として8件くらい見つかったよ〜。**

特に危ないのは、単にエラーになる式より、**正常に lower されたように見えて意味だけ変わる pattern 系**だねぇ。

> 注: 現行実装と `archive` の静的照合。実行していない箇所は「濃厚」と分けたよ〜。

| 優先度 | 移植漏れ                                     | 判定   |
| --- | ---------------------------------------- | ---- |
| S   | `true` / `false` pattern                 | ほぼ確実 |
| S   | 裸の nullary constructor pattern（`nil` など） | ほぼ確実 |
| S   | `do` continuation marker                 | 確定   |
| A   | rule の lazy quantifier `*?` / `+?`       | 確定   |
| A   | record 値の head/tail spread               | 確定級  |
| A   | i64 を越える整数 literal / pattern             | 確定   |
| B   | destructuring 内の `$x`                    | ほぼ確実 |
| B   | field 後の qualified path `x.foo::bar`     | 確定級  |

---

## 1. `true` / `false` pattern が変数束縛へ化ける

これはかなり危ない。

旧作は pattern lowering の冒頭で `true` / `false` を `Lit::Bool` として認識していた。constructor 解決も、その後の変数束縛より先に試していた。

現行の本番 lowerer は、constructor spine でも symbol でもない裸の `Ident` を、そのまま新しい local binding にしている。bool 専用分岐がない。

つまり、これが

```yu
my f b = case b:
    true -> 1
    false -> 0
```

概念上こうなる恐れが強い。

```text
case b:
    <変数 true へ束縛>  -> 1
    <変数 false へ束縛> -> 0
```

先頭 arm が何にでも match するので、`false` arm へ届かない。

しかも標準ライブラリの junction が、まさに source 上の `true` / `false` pattern を使っている。

`if` lowering 自体は内部で bool pattern を直接合成しているため、一見すると bool match が動いているように見える。ここが発見を遅らせる罠だねぇ。

---

## 2. 裸の nullary constructor pattern が変数束縛へ化ける

同じ根から生えてる別症状。

現行の `pattern_is_constructor_spine` は、次のどちらかでないと constructor 候補にしない。

* qualified path
* payload 付き constructor

一要素の裸名で payload なし、つまり `nil` や `none` や zero-arg variant は候補から落ちる。

その後は普通の identifier binding へ進む。

```yu
enum opt 'a = nil | just 'a

my unwrap_or_zero x = case x:
    nil -> 0
    just y -> y
```

この場合、

* `just y` は payload があるので constructor として扱われる
* `nil` は裸名なので変数 pattern になり、何にでも match する

という非対称が起きそうだねぇ。

興味深いことに、現行には別途 `PatternLowerer` があり、「同名なら nullary constructor を変数束縛より優先する」という正しいロジックと unit testまで入っている。

ただし `PatternLowerer::new` の参照は、そのテスト以外に見つからない。つまり、**正しい resolver は書かれたものの、本番 lowering へ接続されてない**可能性が高い。

### 修正方針

pattern の裸名処理を、概ねこの順に戻すのがよさそう。

1. `_`
2. `true` / `false`
3. scope 内の nullary constructor
4. 通常の変数束縛

ここは最優先だねぇ。option match と junction が静かに誤動作する恐れがある。

---

## 3. `do` continuation marker が丸ごと未移植

現行 parser の式 primary には、今も `"do"` が含まれている。

一方、現行 expression lowerer の token head 分岐は、

* identifier
* sigil identifier
* number
* `...`
* nullfix operator

しか扱わず、`SyntaxKind::Do` は `UnsupportedSyntax` へ落ちる。

旧作では `do` を見たら `state.do_replacement` を埋め込んでいた。

さらに block lowering 側で、

```yu
my x = effectful do
rest
```

の `rest` を lambda として切り出し、`do` の位置へ continuation として渡す処理が一式あった。binding 形式と式形式の両方を処理している。

現行側で `do_replacement` を検索しても archive 側しか出ない。

これはかなり明瞭な丸ごと移植漏れだねぇ。

---

## 4. rule の lazy quantifier `*?` / `+?`

旧作では次の対応になっていた。

```text
*   -> many
+   -> some
*?  -> many_lazy
+?  -> some_lazy
?   -> optional
```

現行は `*`、`+`、`?` を lower する一方、`*?` と `+?` だけ明示的に `UnsupportedSyntax` へ送っている。

```yu
pub main = rule { item*? }
pub other = rule { item+? }
```

この二つが該当するねぇ。

設計メモにも `+?` / `*?` は lazy repetition combinator へ desugar する構文として残っている。

修正自体は比較的小さく、旧作同様 `many_lazy` / `some_lazy` を引く形でよさそう。

---

## 5. record **値**の spread が消えている

旧作の record literal lowering は、先頭または末尾の `..expr` を認識し、方向付きの spread として保持していた。

```yu
my base = {x: 1}

my head = {..base, y: 2}
my tail = {x: 2, ..base}
```

現行の record literal lowerer は field だけを集め、最後に常に

```rust
spread: RecordSpread::None
```

を設定する。

さらに brace group の record 判定も、すべての式が `name: value` 型の inline field であることを要求していて、spread expression を許していない。

一方、現行 poly IR には今も `Head` / `Tail` / `None` が残り、「spread の方向には意味がある」と明記されている。

表面仕様から意図的に落とした可能性はゼロではないけど、IR がそのまま残っているので、**lowering の配線だけ落ちた**と見る方が自然だねぇ。

---

## 6. 大きな整数が `BigInt` にならずエラーになる

旧作の整数 literal は、digit string をそのまま `Lit::Int(String)` に保持していた。i64 の範囲検査はなかった。

現行は digit token を直接 `i64` へ parse している。範囲外なら `InvalidNumber`。

```yu
pub huge = 9223372036854775808
```

これは旧作なら整数として保持できたが、現行では overflow になる。

pattern 側も同じ `parse_number_lit` を使うので、大きな整数 pattern も同様に落ちる。

ところが downstream には、今も `Lit::BigInt` の変換・型付けが揃っている。

つまり current lowering で、

```text
i64 parse 成功 → Lit::Int
i64 parse 失敗かつ全桁数字 → Lit::BigInt
```

とする入口だけ抜けてるように見える。

---

## 7. destructuring 内の mutable sigil `$x`

単純な

```yu
my $x = 1
```

は現行に専用処理がある。

ただし旧作は pattern 全体を再帰走査し、tuple・list・record 内に現れる `$x` についても、

* 初期値 binding `#x`
* reference binding `&x`

を作っていた。

現行は binding の最初の名前だけを取り、その名前が `$` で始まるかを見る。

そのため、少なくとも次の二形が怪しい。

```yu
my ($x, y) = (1, 2)
```

先頭名が `$x` なので、tuple binding 全体が単一 mutable binding 用経路へ誤 dispatch される恐れがある。

```yu
my (x, $y) = (1, 2)
```

こちらは通常 pattern 経路へ入り、`$y` という名前そのものを local に束縛する。一方、式 `$y` の読み取りは `&y` を探すので名前が噛み合わない。現行 pattern item は `SigilIdent` を通常の identifier と同じ形で返している。

旧作同様、pattern を再帰走査して sigil binding を別名へ書き換える必要がありそうだねぇ。

---

## 8. field 後の qualified path `x.foo::bar`

現行 parser の仕様上、field の後ろにも path separator を続けられる。

```yu
x.foo::bar
```

旧作 lowerer は field node の直後を覗き、続く `PathSep` を吸い込んで `foo::bar` を qualified method path として解決していた。

現行の tail lowerer は `Field` 自体は扱うものの、後続の `PathSep` を扱う分岐がない。そこへ到達すると `UnsupportedSyntax` になる。

かなりニッチだけど、parser が今も受理する以上、旧互換としては確実に穴だねぇ。

---

## Yumark は別枠

quoted Yumark / `MarkExpr` も現行では式として未完成。ただしこれは旧作からの退行というより、長く parser-only の状態にある機能と見た方がよさそう。

現状は parser node まではあるものの、AST・IR・型付け・runtime semantics が未設計と明記されている。

なので今回の「移植漏れ」リストには混ぜなかったよ〜。

---

# 直す順番

私ならこの順で止血するねぇ。

1. **裸名 pattern resolver**

   * `true` / `false`
   * nullary constructor
   * 変数束縛
2. **`do` continuation lowering**
3. **rule `*?` / `+?`**
4. **BigInt literal / pattern**
5. **record value spread**
6. **destructuring `$x`**
7. **field 後 qualified path**

特に1番目は、エラーにならず間違った arm が選ばれる類なので最優先。現行に眠ってる `PatternLowerer` を本番経路へ統合するところから始めるのが筋よさそうだねぇ。
