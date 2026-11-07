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

**ユーザーの意向（2026-11-07）**: role で書いて、組版は自前の実装を組む。トランスパイル（外部のツール向けの文字列を作って渡す）は、境界ごとに作って捨てる分だけ効率が悪い。
以下は、この意向のもとで、B の具体化を詰めるためのメモ。決めるのはユーザー。

### B の分かれ目: 値を作る命令を、role にどう書くか

`role` の method は receiver（`a.add` の `a`）を前提に書かれている（spec 6.1）。tagless final の命令（`text: str -> 'r`）は、receiver を持たない。

| 形 | 書き方 | 利点 | 気になる点 |
| --- | --- | --- | --- |
| B1. 戻り値の型で決まる member | `role Doc 'r:` に receiver の無い member（`our text: str -> 'r`）を書く | 本来の tagless final。`d.` を渡さず、文書の型が `'r where 'r: Doc` になる | member の宣言の書き方が spec に無い（要決定）。`default ()`（spec 6.3）が同じ性質の例として出るが、宣言は載っていない |
| B2. backend の値を receiver にする | `role Doc 'b:` に `type out` と `our b.text: str -> out` を書く。backend は `struct html` のような目印の値 | 今の spec の機能だけで書ける（`Index` の `type value` と同じ形） | `d` を毎回渡す。A に近い |

B1 の注意:

- 文書を `my doc = text "x"` のような**値の束縛**で作ると、弱多相になる（spec 4.7）。制約はファイルの終わりまで待ち、決まらなければエラーになる（spec 6.3）。文書は関数にするか、型で決める。
- 搬送の型が `str` のままだと、HTML と TeX の `impl` が衝突する。backend ごとに別の型（`struct html_doc` など）を持つ。
- 辞書（証拠）は呼び出し側で決まる（spec 6.2）。実行時の最適化の余地は、実装側の仕事。

**決定（ユーザー, 2026-11-07）**: **B1**。receiver の無い member は必ず引数を取る（`()` でもよい）。`spec/06-roles.md` 6.1 に確定として入れた。整合条件 K1 は要確認。
値制限を避けるのは「命令が引数を取る」ことではなく、**文書の束縛が関数であること**（`my doc = text "x"` は適用の式なので弱多相になる）。
Yumark が文書を展開するとき、引数なしの命令に `()` を補い、文書を `my doc () = ...` のように unit を受ける関数にすれば、値制限と無縁になる（Yumark 側の設計）。
文書は method 記法を使わず、命令を普通の関数として呼ぶので、method 解決とは干渉しない。

## 文書型の検討（ユーザーの案, 2026-11-07。検討中）

B1 を決めたあと、ユーザーが文書の型について、もう少し考えたいと言った。二つの案を、言われたまま記録する。

**案 R（role の output）。** 型推論が高速にできるなら、という条件つき。

```text
role Doc 'output:
    pub render: self -> 'output
```

文書は自分の型（`self`）を持ち、`render` で出力 `'output` に変えられる。role の中に `concat`（出力の後ろに文字列を足す）などを入れて、`'output` についての操作を、最後の型解決でまとめて決める。
（`self` という型の書き方は spec 6.1 に無い。ここでは案の説明のための仮の書き方で、パース検査していない。）

**案 K（output の kind）。** 案 R が成り立たないとき。`'output` を完全に多相にするか単相にするかの二択になってしまうので、`doc` 型に output の kind を持たせる。
`doc(*)` や `doc(html, latex)` のように、その文書が出せる出力の集合を型に持たせ、命令を使うたびに集合を削っていく。

### 私の分析（決定ではない）

- **案 K は、型の核に新しい種類を足す。** 出力の集合を型の引数にして、命令ごとの共通部分を取る規則が要る。effect 行に近い仕組みで、M1（Lean で証明中の型推論の核）に新しい行の種類を足すことになる。
- **案 R でも、「じわじわ削る」は書けるかもしれない。** 出力ごとの能力を role に分ける（`HtmlRaw` は html 専用の命令など）と、命令を使うたびに `'r where 'r: Doc, 'r: HtmlRaw` のように制約が積まれる。完全多相と単相の間に、「制約つきの多相」がある。
- ただし**開世界か閉世界か**が違う。role 制約は、使う場所から見える `impl` を満たす型なら何でもよい（spec 6.2）。案 K は、出力の集合を型が明示する閉世界。
- **終端の解決。** `'output` が決まらないまま残ると、ファイルの終わりでエラーになる（spec 6.3）。案 R は、最後の型で出力を固定する使い方になる。
- **速さは未検証。** 一つの型変数に積む制約が、能力の role の数に比例する形になる。数を小さく保てば軽いはずだが、M1 の求解が出るまで測れない。
- **文書の持ち方。** `self` 型の値（初期表現）と、`'r: Doc` を満たす多相な式（終端表現、B1）は、同型。AST の型を `Doc` の自由な `impl` にすれば、両方が使える。どちらを主にするかは、ユーザーに確認したい。

### 確認（ユーザー, 2026-11-07）: 文書は自分の型を持つ値（初期表現）

`render: self -> 'output` の `self` は、AST のような初期表現の文書の型。`render` が、出力 `'output` への解釈になる。

**今の spec の構文でも書ける。** `self` を新しい型の書き方にしなくても、role の最初の型引数を文書の型にすればよい（`Index 'container 'key` の `'container` が receiver なのと同じ）。

```yulang
role Doc 'doc 'output:
    our doc.render: 'output

role Output 'o:
    our empty: () -> 'o
    our o.push: str -> 'o
```

`doc.render: 'output` は、receiver を適用した後の型（`Add` の `a.add: 'a -> 'a` と同じ読み）。`impl Doc my_doc html` と `impl Doc my_doc latex` を別々に書き、`my s: html = d.render` のように、結果の型で選ぶ。
出力を組み立てる側（`concat` に当たる部分）は、`Output 'o` のような別の role にすると、`empty` に **B1（receiver の無い member）がそのまま使える**。`'output` の操作は、`'output: Output` の制約として、最後の型解決で決まる。

**初期表現にしたことで変わる点。**

- **出力ごとの能力が、型に自動では出ない。** 終端表現（B1）なら、`HtmlRaw` のような命令を使うと `'r: HtmlRaw` の制約が積まれた。初期表現では、html 専用の node も同じ AST の構成子で、`latex` への `render` が、その node をどうするかが型に現れない。
  - (1) 対応しない node は、`render` のときの実行時の扱い（エラー値、または代替の表示）にする。
  - (2) 案 K のように、文書の型に出力の集合を持たせる（`doc(html, latex)`）。
  - (3) 初期表現を、終端表現から作る（AST を `Doc` の自由な instance にする）。著者は終端表現で書き、能力の制約は終端側で検査し、AST は解析（目次・脚注・相互参照）のために使う。
- **私の推奨（取り下げ, 2026-11-07）**: 最初は (1) としたが、ユーザーが「型を消す」方向に納得していない。下の「型を消さない案」を先に検証する。
- 初期表現には、見出しを集めて目次を作る、脚注を番号づけする、のような**文書全体の解析**が書きやすい利点がある。

### 型を消さない案: AST を polymorphic variant にする（私の案, 2026-11-07。**不採用**, 理由は「方向」の節）

ユーザーの懸念: 「この文書は latex に出せるか」が、実行するまで分からなくなるのは気に入らない（型で守れていたものを手放したくない）。
上の (1)（実行時の扱いにする）は取り下げる。代わりの道:

文書の node を、専用の `doc` 型の構成子ではなく、**polymorphic variant の tag** にする。文書の値の型は、使った tag の和（positive の位置の `|`）として、推論で自動的に決まる。
バックエンドは、扱える tag だけを `case` の arm に並べた関数にする。spec 3b.4 のとおり、polyvariant の pattern だけの `case`（`_` なし）は、入力の型が**閉じる**ので、扱えない tag を含む文書を渡すと型エラーになる。

```yulang
my intro = :section "Access log" (:list [:item "a", :item "b"])
my raw_note = :html_raw "<hr>"

my render_latex d = case d:
    :text s -> s
    :section title body -> "\\section{%{title}}%{render_latex body}"
    :list items -> "\\begin{itemize}%{render_latex items}\\end{itemize}"
    :item s -> "\\item %{s}"

my render_html d = case d:
    :text s -> s
    :section title body -> "<h2>%{title}</h2>%{render_html body}"
    :list items -> "<ul>%{render_html items}</ul>"
    :item s -> "<li>%{s}</li>"
    :html_raw s -> s
```

期待する型（未検証）: `render_latex` は `:text` / `:section` / `:list` / `:item` だけを受ける。`raw_note` は `:html_raw` を含むので `render_latex raw_note` は型エラー、`render_html raw_note` は通る。

- 新しい種類は要らない。spec が既に持つ variant の tag の行（4.7b）と、閉じた `case`（3b.4）だけで、案 K の「出せる出力の集合」が、使った tag の集合として自然に出る。
- 開世界のまま、利用者が自分の node（tag）を足せる。バックエンドが `_` の arm を持てば、未知の tag を受ける（実行時の扱いを選ぶ道は、`_` として残る）。
- 子の文書を含む node は、再帰する variant 型になる（spec 10.21 の正則な再帰型）。型の表示が長くなることはありうる。
- **要確認**: role との関係。`impl Doc ... latex` の head に variant の行を置けるか（spec 6.2）。置けなければ、`render_latex` は role を介さない関数として並べる。出力ごとに関数名を持つ形でよいか。
- **未検証**: 再帰する開いた variant の推論が、M1 で通るか。速いか。型の大きさ（使った tag の数）に比例して重くならないか。
- 注意: 引数のない `my render_latex = case:` は自分を呼べない（spec 2.1）ので、引数 `d` を取る形で書いた。

## 方向（ユーザー, 2026-11-07）

出力は文字列ではなく、`html` / `latex` / `pdf` のような**実際の型の値**として出す。文字列にすると、PDF が出せない。画像や音声のような出力も要る。
出力の種類（と node の種類）を後から足せることが要るので、expression problem を解く道と一緒に考える必要がある。その意味で、polymorphic variant の AST 案（上）は、出力の側を解かないので**採らない**。

進める形: 出力できる role を考える。`Doc 'container 'output` が有望（ユーザーの見立て）。型推論が速いことが前提。

```text
role Doc 'container 'output:
    ...        # 具体的な member は未定
```

未決（ユーザーの判断を待つ。私は決めない）:

- `'container` は何を表すか（文書の入れ物の型か、node の集合か）。
- 出力の型（`html` など）を、どの role で組み立てるか。上の `Output 'o`（`empty` は B1 で書ける）をその位置に使うのか。
- K1（receiver の無い member の整合条件、`spec/06` の「確認してほしい点」）。
- 多引数の role `Doc 'container 'output` の解決が、M1 の求解で速いか。M1 が仕上がってから測る。

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

1. （決定済み）B1。K1（role の型引数が戻り値に現れない member の扱い）を決める。
2. PDF の最初の道は a か。組版モデルの `spec/` を、出典つきで小さく書き始めてよいか。
3. Yumark の command を、どの形の呼び出しに対応させるか（Yumark の設計と一緒に）。
