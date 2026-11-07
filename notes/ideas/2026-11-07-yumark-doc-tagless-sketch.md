# スケッチ: ログ集計から文書を出す (Yumark と tagless final) (2026-11-07)

状態: **スケッチ。決定は無い。** 構文は `syntax_guide_check` でパース検査した範囲まで。型が通るか、実行して動くかは**未検証**
(型推論の核 M1 が未完で、実行系はこのブランチに無い)。std の関数名(`tally`、`join` など)は仮。
署名: Claude (Sonnet 5.5)。案の発案はユーザー（2026-11-07 の雑談）。

## ねらい

- bash や Perl の代わりに使える。
- 同じ言語で、文書も書ける。数式入りの PDF が出れば最良。
- ログ集計の結果を、そのまま文書として出せる。

## 一本の流れ

```text
ログ → parser DSL で切る → 集計 → 文書の値 → HTML / TeX / (PDF)
```

### 1. 集計

```yulang
my resource_of = case:
    ~"GET :resource" -> resource
    _ -> "other"

my summarize lines = lines | map resource_of | tally
```

`case:` は、対象を取る一引数の関数になる（spec 3.7）。`~"GET :resource"` は parser pattern（spec 9.1）。
`tally`（要素ごとの個数）は仮の名前。

### 2. 文書を、バックエンドを受け取る関数として書く

```yulang
my report counts d =
    d.section "Access log" (d.list (counts | map \(name, n) -> d.item "%{name}: %{n}"))
```

`d` は「文書の命令を持つ record」。`report` は、`d` に **`section` / `list` / `item` を持つこと**だけを要求する。
spec 4.3 の「必須 field が主型に出る」推論が効けば、`report` の型は、使った命令の集合を自分で語るはず（未検証）。

### 3. バックエンドは、命令を実装する record

```yulang
my html = {
    section: \title body -> "<h2>%{title}</h2>%{body}",
    list: \items -> "<ul>%{std::text::join "" items}</ul>",
    item: \text -> "<li>%{text}</li>",
}

my tex = {
    section: \title body -> "\\section{%{title}}%{body}",
    list: \items -> "\\begin{itemize}%{std::text::join "" items}\\end{itemize}",
    item: \text -> "\\item %{text}",
}
```

`report counts html` で HTML、`report counts tex` で TeX になる。同じ原稿で、差し替えるのは `d` だけ。

## tagless final を、Yulang でどう書くか（三案）

| 案 | 形 | 利点 | 気になる点 |
| --- | --- | --- | --- |
| A. record を渡す（上のスケッチ） | 文書は `d` を受ける関数 | 仕様に既にある機能だけで書ける。使った命令が型に出る | `d.` を毎回書く。命令が増えると record が大きい |
| B. `role` で書く | `role Doc 'r:` に命令を並べ、バックエンドは `impl` | 構文が型クラス風で、`impl` の切り替えが言語機能になる | role の method は receiver（`a.add`）を前提にしている。receiver の無い命令（`text: str -> 'r`）を書ける形が spec に無い（要決定） |
| C. effect で書く | 命令は `act` の operation、バックエンドは `catch` の handler | 文書を直接形式で書ける（`doc::section "..."` と呼ぶだけ）。Yulang らしさが最も出る | 出力の組み立てを handler にどう持たせるか、shallow handler で継続を扱う設計が要る |

```yulang
act doc:
    our section: str -> ()
    our item: str -> ()

my report_fx counts =
    doc::section "Access log"
    for (name, n) in counts:
        doc::item "%{name}: %{n}"
```

案 C の書き味は良いが、バックエンドを書くコスト（handler）と、出力を貯める方法が設計の本体になる。

**私の推奨**: 最初の一本は **A**。理由は、spec が既に約束している機能（record、field 要求の推論）だけで、型に「使う命令」が出るところまで確かめられるから。
B と C は、A の上に重ねられる（C は、命令を呼ぶ糖衣として）。

## Yumark の TeX 風コマンドとの関係

Yumark の command（`\emph{...}` のような形。`notes/design/2026-09-01-doc-comment-yumark-addendum.md`）は、文書の中の呼び出しとして読める。
上の `d.section ...` が、Yumark の command に対応するなら、**Yumark の原稿は「`d` を受ける関数」に解釈する**という形にできるかもしれない。
この対応は、Yumark の設計（command が値を返すか、どの引数が Yulang 式か）と合わせて決める必要がある。ここでは決めない。

## 値制限との関係（要確認）

文書を `my doc = d.section ...` のように**値の束縛**で作ると、関数適用を含むので弱多相になり、バックエンドを二つに使い分けられないかもしれない（spec 4.7）。
A の形（文書を関数 `my report counts d = ...` として書く）なら、この問題に触れないはず。M1 が仕上がったら、実際に確かめる。

## PDF と数式

組版エンジンの選択肢。判断はユーザー。

| 道 | 内容 | 利点 | 気になる点 |
| --- | --- | --- | --- |
| a. 外部エンジンに渡す | TeX か Typst の入力を出力して、外部コマンドで PDF にする | 最も細い線で、数式も既存の品質 | 外部の依存が残る。「一本で完結」の売りが弱まる |
| b. Rust の既存部品で組む | フォントの読み取り（`ttf-parser`）、整形（`rustybuzz`）、PDF 書き出し（`krilla` / `pdf-writer`）を使い、改行と数式の配置は自前 | 依存が Rust の crate で、単体の実行体にできる | 改行・数式・CJK の組版は大きな仕事 |
| c. Typst を library として使う | Typst は Rust 製で Apache-2.0。組版・数式・PDF 出力を持つ | 動く完成品がある | Typst 自体が一つの言語で、役割が重なる。Yulang の型としての薄い包みになる |
| d. SATySFi の設計を Rust に移す | PDF と組版を扱うデータ型を、言語仕様に入れる | SATySFi が、型つき組版の前例を示している | 下記のライセンスの確認が先 |

- SATySFi は [LGPL-3.0](https://github.com/gfngfn/SATySFi)。そのコードを Rust に**書き写す**なら、派生物になる可能性が高く、Yulang 側のライセンスとの整合を決める必要がある。
  設計（何を型にして、組版の過程をどう分けるか）を**参考に、独立に実装する**場合の扱いは別の話で、私は法的判断をしない。ユーザーが決めること。
- Typst の crate 群は [Apache-2.0](https://docs.rs/crate/typwriter/latest) で、[krilla](https://github.com/LaurenzV/krilla) は MIT / Apache-2.0（調べたのは検索結果の範囲）。`pdf-writer` / `rustybuzz` / `ttf-parser` の個別のライセンスは未確認。
- 「PDF を扱うデータ型を言語仕様に入れる」のは、`std` と実行系の境界の設計になる（spec 8.5）。実行系が戻ってからの仕事。

**私の推奨**: 最初は a（TeX / HTML を出す）で、文書の側の設計を固める。PDF の型は別の大きなプロジェクトとして切り出し、d を選ぶなら先にライセンスの方針を決める。

## ユーザーに決めてほしいこと（順番に）

1. tagless final の最初の形は A でよいか。
2. PDF の最初の道は a か。d を狙うなら、ライセンスの方針（移植か、独立実装か）。
3. Yumark の command を、どの形の呼び出しに対応させるか（Yumark の設計と一緒に）。
