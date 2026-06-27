# Yulang

```yulang
if all [1, 2, 3] < any [4, 5, 6]:
    "found a pair"
else:
    "nothing"
```

この `if` は、左のリストの要素ひとつひとつを、右のリストの要素全部と比較しています。ループも内包表記も補助関数もありません。`all` と `any` がただの値で、比較演算子の方がそれらを持ち上げるからです。同じ仕掛けが、非決定的な探索にもそのまま効きます。

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..
    guard: a * a + b * b == c * c
    (a, b, c)
}.once
```

3 つの `each` が、無限に広がる 3 次元の格子を探索します。`guard` で枝刈り、`.once` で「最初に見つかった 1 件」を取り出す。書かれているコードは上から下にまっすぐ流れているのに、裏側では分岐と backtrack が走っています。

Yulang の中心にあるのは、**「制御構文はライブラリで書く」** という方針です。可変参照も、非決定性も、`all` / `any` のような集合的な比較も、early return も、型付きエラーも、独自の backtrack も — どれも parser が抱える builtin ではなく、代数的エフェクトという 1 つの仕組みの上に乗った普通の関数です。表に出るコードは短くて直線的なまま、裏側の形だけを好きに広げられます。

## 中に入っているもの

- **代数的エフェクトと handler。** `act` で operation を宣言し、`catch op, k -> ...` で受けます。handler は捕まえた継続 `k` を受け取るので、再開・再試行・中断はすべて「`k` をどう扱うか」の選択として書けます。
- **typeclass じゃなくて role。** `role Add 'a:` で interface を宣言し、`impl Add int:` で実装。method は普通のドット呼び出しに見えます。
- **可変な local binding。** `my $x = 0` で宣言、`$x` で読み、`&x = v` で書く。中では handler 付きの `var` effect に展開されるので、意味論は純粋なまま、書き味は素朴です。
- **binding の左辺は全部 pattern。** `my (a, b) = pair` も、record pattern + default で書く optional 引数 `my area {width = 1, height = 2} = width * height` も、同じ binding の形です。
- **括弧少なめの表面。** bare application `f x y`、colon application `f: ...`、`:` とインデントで開く layout block。

::: tip Playground
このページの例はすべて <a href="/" target="_self">Playground</a> でそのまま動きます。
:::

## 次に読むもの

- [インストール](./install) — CLI を入れて最初の `.yu` ファイルを動かす
- [ツアー](./tour) — Yulang の主要機能を一通り見る
- [クックブック](./cookbook) — タスク指向の短いレシピ集
- [落とし穴](./pitfalls) — 引っかかりやすい挙動と回避策
- [キャッシュ](./cache) — ローカル CLI の artifact cache と route label
- [リファレンス](/ja/reference/) — 構文と意味の詳細
