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

前提（ユーザーの説明, 2026-11-07）: 実装の**移植**が目的ではない。組版の挙動には正確な仕様が無いので、挙動を明示的に書いてある実装（SATySFi、Typst など）を**仕様の代わりに読み**、自前で独立に書く。速さは Rust で素直に書けば足りる。

部品ごとには、公開された仕様がある。足りないのは、それらを組み合わせた最終的な見た目の決まり方で、そこは参照実装の挙動が事実上の仕様になる。

| 部品 | 仕様の所在 |
| --- | --- |
| PDF のファイル形式 | ISO 32000 |
| フォント、数式用の MATH テーブル | OpenType の仕様 |
| 改行の候補、両方向文字 | Unicode UAX #14、UAX #9 |
| 段落の改行の最適化 | Knuth–Plass の論文 |
| 数式の配置 | TeXbook の Appendix G |
| 上の組み合わせ方（最終の見た目） | 無い → 参照実装の挙動 |

進め方の案:

1. `spec/` に自前の組版モデルを書く。各文に出典（上の仕様、または「どの参照実装のどの挙動か」）を付ける。
2. 参照実装との出力の差分でテストする（Lean の oracle 計画 `2026-11-06-rust-oracle-plan.md` と同じ発想）。
3. 実装は Rust で独立に書く。使う既存部品は、ライセンスを確認してから選ぶ。

実装の道:

| 道 | 内容 | 利点 | 気になる点 |
| --- | --- | --- | --- |
| a. 外部エンジンに渡す | TeX か Typst の入力を出力して、外部コマンドで PDF にする | 最も細い線で、数式も既存の品質 | 外部の依存が残る。「一本で完結」の売りが弱まる |
| b. Rust の既存部品で組む | フォントの読み取り（`ttf-parser`）、整形（`rustybuzz`）、PDF 書き出し（`krilla` / `pdf-writer`）を使い、改行と数式の配置は自前 | 依存が Rust の crate で、単体の実行体にできる | 改行・数式・CJK の組版は大きな仕事 |
| c. Typst を library として使う | Typst は Rust 製で Apache-2.0。組版・数式・PDF 出力を持つ | 動く完成品がある | Typst 自体が一つの言語で、役割が重なる。Yulang の型としての薄い包みになる |

- 参照実装を**読んで挙動を知る**ことと、コードを**写す**ことは別。SATySFi は [LGPL-3.0](https://github.com/gfngfn/SATySFi)、Typst の crate 群は [Apache-2.0](https://docs.rs/crate/typwriter/latest) で、[krilla](https://github.com/LaurenzV/krilla) は MIT / Apache-2.0（調べたのは検索結果の範囲。`pdf-writer` / `rustybuzz` / `ttf-parser` の個別のライセンスは未確認）。
  独立に書く限り、これは主に「どの挙動をどこから知ったかを出典として残す」運用の問題になる。法的な判断は私はしない。
- 「PDF を扱うデータ型を言語仕様に入れる」のは、`std` と実行系の境界の設計になる（spec 8.5）。実行系が戻ってからの仕事。

**私の推奨**: 最初は a（TeX / HTML を出す）で、文書の側の設計を固める。並行して、組版モデルの `spec/` を、小さな範囲（1 段落の改行）から出典つきで書き始める。PDF の型は、その後に別のプロジェクトとして切り出す。

## ユーザーに決めてほしいこと（順番に）

1. tagless final の最初の形は A でよいか。
2. PDF の最初の道は a か。組版モデルの `spec/` を、出典つきで小さく書き始めてよいか。
3. Yumark の command を、どの形の呼び出しに対応させるか（Yumark の設計と一緒に）。
