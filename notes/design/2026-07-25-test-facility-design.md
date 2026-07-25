# Yulang テスト機構の設計

決定日: 2026-07-25
状態: **提案（ユーザ承認待ち）**
著者: Claude (Opus 5)

この文書は、Yulang でユーザーが自分のコードをテストするための機構の正本である。
コンパイラ自身の回帰を固定する contract manifest（`tests/yulang/cases.toml`）とは別レイヤであり、
両者を混同しない。

## 0. 決定事項

ユーザー決定により、次の 3 つの機構を併存させる。

1. **`assert` を効果として提供する。** 通常実行では表明式を評価しない。
2. **test module。** その中の計算はテスト実行時にのみ走る。
3. **doc comment 内テスト。** 価値の中心は「周囲の環境を参照できる」ことにある。

3 は Rust の doctest と意図的に異なる。Rust の doctest は別 crate としてコンパイルされ、
公開 API しか参照できない。Yulang では、doc comment 中のコードを、その doc comment が
付いている宣言の**字句環境で**評価する。これは「ドキュメントに書いた例が、周囲の文脈を
前提にして書ける」ことを意味する。

## 1. 調査で確定した前提

設計はこれらの事実の上に立つ。実装前に覆っていないか確認すること。

### 1.1 条件付きコンパイルは存在しない

`cfg` 相当の言語機能は無く、CLI にもビルドモード・プロファイル・feature flag は無い。
`--interpreter` はバックエンド選択であり、コンパイル対象の取捨選択ではない。

したがって本設計は、条件付きコンパイルを**新設しない**ことを前提とする。

### 1.2 `notes/todo/property-testing.md` の禁止事項

> テストランナーのために推論・lowering に test 専用分岐を入れること。

これは既存の記録済み禁止事項であり、本設計はこれに従う。1.1 と合わせて、
「テストのためにコンパイラ本体へモード分岐を足す」道は最初から閉じている。

### 1.3 `lazy` は実装済み

`lazy prefix` / `infix` / `suffix` / `nullfix` が実装されており、lowering が被演算子を
thunk 化する。

```
() -> [body effect] body value
```

thunk 生成自体は純粋で、body の効果は戻り側に入る。`lib/std/core/ops.yu` の `and` / `or` が
実使用中である。

さらに、効果操作へ明示的な thunk（`\() -> expr`）を引数として渡し、handler がそれを
捨てた場合、thunk の中身は評価されないことが実機で確認されている。

### 1.4 効果は公開シグネチャへ伝播する

```
pub "std.io.console.println":
  std::text::str::str -> [std::io::console::out] ()
```

効果を実行する関数の公開型には、その効果が残留効果として現れる。
「効果注釈が capability 宣言に縮退する」という既存決定は、注釈が関数全体の exact row を
命令しないという意味であって、実効果の自動消去ではない。

デフォルトで型から効果を消す前例は存在しない。host act は user handler が無ければ
root runtime registry が処理するが、効果行には残る。

**この伝播は正しい挙動として受け入れる。**（ユーザー判断、2026-07-25）
Koka の `total` と同様、効果が型に付いて回ること自体が言語の性質である。
「見せたくない」は表示の問題であり、意味論を歪める理由にはならない。
表示を制御したい場合は、既存の public type projection 層
（`notes/design/2026-07-03-hover-public-type-projection.md`）で解決する。

### 1.5 module の入れ子と可視性

- 子 module は親の `my` 束縛を参照できる（実機確認済み）。
- module 内容がモード・可視性・未使用を理由に除外されることは無い。未使用の inline module
  内に未解決名があればコンパイルは失敗する。
- `my mod` は現行の statement parser で module 宣言にならない。`our mod` / `pub mod` は動く。
- 修飾パス経由で `my` メンバーが読める既知バグがある。
  `notes/bugs/2026-07-25-module-visibility-qualified-path-leak.md` を参照。

### 1.6 doc comment の保持内容

- `--`（行 doc）と `---`（ブロック doc）はいずれも lossless な Yumark CST として保存され、
  各 token / node が `text_range` を持つ。
- 直後の宣言と空行なしで隣接する doc は、`DefId` または `TypeDeclId` を key に関連付く。
- **字句環境は保持されていない。** `DocCommentUnit` に `ModuleId` / `ModuleOrder` /
  scope snapshot の欄は無く、hover の render input key は明示的に "independent of source
  location" である。lazy renderer は embedded std だけを持つ合成 source でコンパイルする。
- info 文字列が `yulang` の code fence は、パーサが既に Yulang CST として構文解析している。
  レンダラはそれを実行せず、Markdown fence として再出力するだけである。

つまり機構 3 は、**構文解析は既に済んでおり、不足しているのは字句環境の受け渡しだけ**である。

### 1.7 contract runner の再利用可能部分

転用できる: case 名フィルタ、tag フィルタ（複数指定は AND）、未知 case の事前拒否、
manifest 順の決定的実行、子プロセスの status / stdout / stderr 捕捉、exact / contains 照合、
期待失敗、一時ファイル生成と隔離キャッシュ、非ゼロ終了。

転用できない: TOML `[[case]]` schema、compiler 固有の case 種別、tag taxonomy、
公開シグネチャ・診断の golden 検査。

**現行 runner は fail-fast であり、最初の失敗で `process::exit(1)` する。**
失敗の集約も、全 case の一覧も、timing report も無い。ユーザー向けランナーには集約が要る。

## 2. 決定 T1: `assert` は遅延効果である

### 2.1 綴り

`assert` は std が提供する `lazy prefix` 演算子とする。

```yu
assert x == 1
```

`lazy` により被演算子は `() -> [e] bool` の thunk となり、`assert` の本体へ未評価のまま渡る。

### 2.2 意味論

`assert` は `test` 効果の操作を実行する。操作は thunk と表明地点の情報を受け取る。
評価するか否かは**ハンドラが決める**。

- **テスト実行時**: ランナーが導入したハンドラが thunk を強制し、`false` なら失敗として記録する。
- **通常実行時**: root の既定ハンドラが thunk を**強制せずに捨てる**。したがって表明式は
  評価されず、副作用も走らず、コストは thunk 生成のみになる。

これによりユーザー要求「通常時は計算されない」が、条件付きコンパイル無しで満たされる。

### 2.3 効果行

`assert` を含む関数の公開型には `test` 効果が残る。1.4 の通りこれは受け入れる。

test module や doc comment 内に書かれた `assert` は、そもそも公開表面に現れないため
影響しない。production コードに `assert` を残した場合に型がそれを告げるのは、
情報として正しい。

### 2.4 失敗の表現

表明失敗は**効果として報告する**。値レベルの `result` にも trap にもしない。
`notes/todo/property-testing.md` の既存素描（「失敗は error effect。ランナーが catch して
反例値と一緒に報告する」）と整合する。

これにより、ハンドラの差し替えだけで次を書き分けられる。

- 最初の失敗で停止する
- 全ての失敗を集めて報告する
- 失敗回数を数える（property testing の縮小に必要）

### 2.5 未決

- `assert_eq` 等の派生をどこまで std に持たせるか。最小構成では `assert` のみとし、
  等値比較の差分表示が欲しくなった時点で追加する。
- 表明地点の情報（source range）をどう運ぶか。効果操作の引数として明示的に渡すか、
  診断側の provenance に載せるか。後者なら
  `notes/design/2026-07-21-constraint-provenance-redesign-spec.md` の機構が使える可能性がある。

## 3. 決定 T2: test module は常にコンパイルされ、実行だけがテスト時に限られる

### 3.1 綴り

`mod` の直後に置く `test` マーカーで宣言する。（ユーザー決定、2026-07-25）

```yu
mod test:
    ...

mod test parser:
    ...

my mod test internals:
    ...

mod test suite;
```

文法は次のとおり。

```text
[visibility] mod test [name] ( ";" | "{" ... "}" | ":" ... )
```

- **`mod` の直後の `test` は常にマーカーであり、module 名ではない。**
  したがって `test` という名前の通常 module は綴れない。これは意図した制約である。
  「`test` という module 名は test の時にしか作らない」という観察を、構文で真にすることで、
  `mod test { }` と `mod test foo { }` が構造的に別物になる曖昧さを消す。
- 名前は省略できる。`mod test:` は名前なしの test module である。
- 名前を付ければ複数持てる。`mod test parser` と `mod test lowering` を並べられ、
  失敗報告も module 名で区別できる。
- 可視性と直交する。`my` / `our` / 省略がそのまま効く。`our` は既定なので、
  通常は `mod test name:` と書けばよい。
- 外部ファイル形式 `mod test name;` を認める。sibling の `name.yu` を test module として
  読み込む。テストを本体と別ファイルに置ける。

`test` は予約語にしない。`mod` の直後という位置でのみ意味を持つ文脈キーワードとする。
`test` は識別子として自然に使われる語であり（`my test = ...` は普通に書く）、
大域的に奪うのは損である。

parser 実装上の注記。

- `mod test` の次のトークンが識別子なら名前あり、`;` / `{` / `:` なら名前なしと解する。
- 現行 parser では `my mod` が module 宣言として解釈されない（1.5）。本決定は
  `my mod test name` を認めるため、その欠落もここで解消する。
  `notes/bugs/2026-07-25-module-visibility-qualified-path-leak.md` の追記事項も参照。

### 3.2 意味論

- test module の内容は**常にコンパイルされる**。条件付きコンパイルは導入しない（1.1、1.2）。
  これは副作用ではなく利点である。テストコードが本体の変更に追随せず腐った場合、
  テストを走らせるまでもなくコンパイルが失敗して気づける。
- test module 内の計算は、**ランナーが呼び出した時にのみ実行される**。通常の実行経路は
  test module のメンバーを起動しない。

ユーザー要求「その中の計算は test の時しか実行されない」は、この「実行」の水準で満たす。

### 3.3 親の非公開束縛への参照

子 module は親の `my` を参照できる（1.5、実機確認済み）。これは test module にとって
本質的な能力であり、意図的に維持する。テストが実装の内部に触れられなければ、
テストとして弱い。

### 3.4 発見規則

ランナーは、**`test` マーカーを持つ module** を探索し、その束縛をテストとして実行する。

名前ではなく構文マーカーで発見することが重要である。命名規約による発見は、
名前を変えた途端に静かにテストが走らなくなるという失敗様式を持つ。マーカーならその事故が無い。

厳密な発見規則（入れ子の扱い、単一 module 内の複数テスト、どの束縛をテストとみなすか）は
実装時に確定する。`notes/todo/property-testing.md` は `test "名前":` ブロックの導入を
将来課題として残しており、本設計はそれと矛盾しない。当面は test module + 通常の束縛で始め、
専用構文が必要になってから足す。

### 3.5 未決

- test module の内容が本体のバイナリに含まれてしまうか。現状 module 内容は常にコンパイル
  されるため、そのままでは含まれる。実害の有無（サイズ、公開表面）を測ってから、
  必要なら dead-code 除去の水準で扱う。言語機能としての条件付きコンパイルは導入しない。

## 4. 決定 T3: doc comment 内テストは documented item の字句環境で評価する

### 4.1 対象

doc comment 中の、info 文字列が `yulang` の code fence を対象とする。
他の info を持つ fence は従来どおり不透明なテキストとして扱う。

### 4.2 意味論

fence 内のコードは、その doc comment が付いている宣言の**字句環境**で評価する。
すなわち、その地点で見えている名前（親 module の `my` を含む）を参照できる。

これがユーザーが機構 3 に求めた価値そのものである。

### 4.3 不足している配線

1.6 の通り、構文解析は済んでいるが字句環境が保持されていない。必要な追加は次の一点に集約される。

- `DocCommentUnit` に、その doc が属する `ModuleId` と `ModuleOrder`（宣言地点の source order）
  を保持させる。

これは観測情報の追加であり、推論・lowering の意味論を変えない。1.2 の禁止事項に抵触しない。

### 4.4 レンダリングとの分離

Yumark の正本設計（`notes/design/2026-07-08-yumark-value-model-tagless-final.md`）は既に
両者を分離している。

> Document rendering: always treated as plain source text — never executed.
> Test execution: a future, separate doctest-style test runner — not yet built.

本設計はこの分離を維持する。**レンダラは今後も fence を実行しない。**
doctest ランナーは独立した consumer として同じ CST を読む。

### 4.5 未決

- fence 内が式なのか宣言列なのか、表明を書けるのか（`assert` を使えるのか）。
  T1 の `assert` が使えることが自然だが、字句環境に `assert` が見えている必要がある。
- 失敗時に報告する source range を、doc comment 内の相対位置から元ファイルの絶対位置へ
  どう写像するか。`text_range` は保持されているので機構はある。

## 5. 共通: ランナー

### 5.1 起動

`yulang test` を新設する。contract runner（`yulang contract`）とは別コマンドとし、
manifest も共有しない。

### 5.2 再利用

1.7 の「転用できる」部分を再利用する。特に子プロセス捕捉、フィルタ、非ゼロ終了。

### 5.3 集約

現行 contract runner の fail-fast は、コンパイラ回帰には適切だがユーザーのテストには適さない。
`yulang test` は**全テストを実行し、結果を集約して報告する**。

### 5.4 未決

- 出力形式。既存の構造化診断（`SourceDiagnostic`）を再利用できるか、テスト結果は別の形が
  適切か。
- playground / LSP からの利用。`notes/todo/testing.md` は「将来の `yulang test` / playground /
  LSP canary も同じ manifest を読む前提にする」と書いているが、本設計はユーザー向けテストに
  manifest を使わないため、その前提は本設計には引き継がない。

## 6. やってはいけないこと

- 条件付きコンパイル（`cfg` 相当）をテストのために言語へ導入すること。
- 推論・lowering にテスト専用の分岐を入れること（既存の禁止事項）。
- 効果の伝播をテストのために特別扱いして型から消すこと。表示の問題は表示層で解く。
- Yumark レンダラに fence の実行を持ち込むこと。レンダリングと実行の分離を壊さない。
- ユーザー向けテストを contract manifest（`cases.toml`）の上に載せること。
  contract はコンパイラ自身の回帰固定であり、対象読者も更新頻度も異なる。

## 7. 実装の順序（案）

各スライスは、着手前に前スライスの結論が覆っていないことを確認する。

- **TEST-A**: `assert` を std に追加する（`lazy prefix`、`test` 効果、root 既定ハンドラで破棄）。
  通常実行で表明式が評価されないことを実機で確認する。規模 M。
- **TEST-B0**: parser に `[visibility] mod test [name]` を追加する。inline 形と外部ファイル形の
  両方。併せて `my mod` が宣言にならない既存の欠落を解消する。この時点ではマーカーを保持する
  だけで、実行時の扱いは変えない。規模 S-M。
- **TEST-B**: `yulang test` の骨格。マーカーによる test module の発見と実行、結果の集約報告。規模 M。
- **TEST-C**: `DocCommentUnit` へ `ModuleId` / `ModuleOrder` を保持させる。観測のみで、
  既存の診断・スキーム・出力が不変であることを確認する。規模 S。
- **TEST-D**: doctest ランナー。TEST-C の環境情報を使って fence を字句環境で評価する。規模 M。
- **TEST-E**: 検証一式。std / examples / contract 全ゲート、および表明を含むコードの
  公開シグネチャが期待通り `test` 効果を持つことの固定。規模 M。

TEST-A、TEST-B0、TEST-C は互いに独立しており、順序を入れ替えてよい。
TEST-B は TEST-B0 に、TEST-D は TEST-A と TEST-C の両方に依存する。

## 8. 停止して確認すべき条件

- `assert` の root 既定ハンドラを入れた結果、既存プログラムの効果行や公開シグネチャが
  意図せず変わった場合。
- test module の常時コンパイルが、実行バイナリのサイズや公開表面に無視できない影響を与えた場合。
- doc comment への環境情報の追加が、既存の hover / render 経路の出力を変えた場合
  （TEST-C は観測のみのはずである）。
- doctest の字句環境評価が、既存の embedded-std 前提の lazy renderer と衝突した場合。
