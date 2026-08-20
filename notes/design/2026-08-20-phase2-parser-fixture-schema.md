# Phase 2 parser compatibility fixture schema（draft）

Status: Claude とユーザーのレビュー待ち。これは正本ではない。

## Problem statement

Phase 0 の compatibility corpus は `tests/contracts/stable-core/v0/` にあり、
`corpus.toml`、case ごとの `main.yu`、`diagnostic.toml` / `case.toml` /
`signature.toml`、stdout / stderr record から成る。この corpus が固定するのは
`yulang2-oracle` に対する whole-compiler の `run`、`check`、`public-signature` の
観測結果である。

Phase 2 の parser recovery / header discovery fixture は、これとは異なる phase
product を固定する必要がある。`docs/yulang3-architecture.md` §4.2.2 が要求する
観測対象は次の通りである。

- `HeaderInfo` の coverage、source-level import、operator signature。
- header discovery と full parse がそれぞれ独立に得た共通 header fact。
- `Missing` が zero-width、`Error` が一 byte 以上を所有する recovery node。
- recovery node と diagnostic の 1 対 1 対応。
- header diagnostic が同じ `DiagnosticId` のまま `ParsedFile` に一度だけ取り込まれ、
  body diagnostic と合わせた whole-file の exhaustive list になること。
- primary range の start / end、recovery event sequence、diagnostic code による
  deterministic な diagnostic order。
- header/full fact mismatch を silent overwrite せず compiler invariant violation とする
  parity contract。
- full CST の source byte conservation と marker balance。

stable-core の end-to-end record だけでは、これらの phase 別の結果と identity を
表現できない。また現在の `crates/yu-syntax/src/lib.rs` は crate boundary だけを持ち、
parse API はまだない。そのため、この文書では Rust の内部表現を先に固定せず、
`HeaderInfo` と `ParsedFile` の public contract を比較するための fixture projection を
定義する。実装時の型名や arena ID の serialization format ではなく、将来の harness が
typed assertion へ変換する入力形式とする。

## Non-goals

- `HeaderInfo`、`SyntaxEnvironment`、`ParsedFile`、`HirModule` や parser pipeline を
  実装しない。
- この slice では実 case、corpus directory、manifest、source file を追加しない。
  本文中の worked example だけを置く。
- full CST dump、rowan の raw kind number、arena ID、marker event stream を snapshot
  しない。
- parser recovery の grammar rule、diagnostic 文言、operator grammar を新たに決定しない。
- §18 で未決定の late `use` の semantic-dependency 上の意味を決めない。
- §18 で未決定の non-header `mod` / late `use` による source-set expansion の発見方法を
  決めない。
- `HeaderInfo` の raw fact を `ModuleId`、syntax dependency graph、semantic dependency
  graph の結論へ変換しない。
- Yulang2 oracle record の採取をこの slice で自動化しない。
- known-divergent parity case を contract の成功形として認めない。未実装の期間に test が
  fail することと、矛盾を期待値として受理することは分ける。

syntax reexport cycle と revision 間の incremental parity は §4.2.2 の fixture family に
必要だが、それぞれ syntax-planning scenario と edit-transition scenario の orchestration
を要する。本 schema は、その scenario が各 source snapshot の期待値として再利用する
atomic parser fixture を定義する。scenario descriptor 自体は `SyntaxEnvironment` と
incremental query の設計時に別途定義し、この atomic schema の意味を変更しない。

## Schema definition

### Format and contract boundary

形式には TOML を使う。UTF-8 source は別の `main.yu` に置き、期待値を
`fixture.toml` に置く。TOML は phase ごとの table、ordered list、optional oracle record
を素直に表現でき、stable-core の manifest + per-case source という運用も引き継げる。
source を TOML multiline string に埋め込まないため、改行や末尾 newline を含む入力 byte
を oracle と harness で共有できる。

すべての range は `main.yu` の UTF-8 byte offset による half-open range `[start, end)`
とする。line / column は表示上の派生値であり、fixture identity には使わない。array の
並びは期待順を表し、table / inline table の key 順は意味を持たない。fixture に書かれて
いない import、operator、recovery node、diagnostic は「期待しない」という closed-world
解釈にする。

root の `corpus.toml` は次の shape を持つ。

```toml
schema_version = 1
contract = "phase2-parser"
contract_version = 0
corpus_revision = 1
frozen_at = "YYYY-MM-DD"
case_count = 0
offset_encoding = "utf-8-bytes"
case_root = "cases"

[files]
source = "main.yu"
expectation = "fixture.toml"

[defaults]
syntax_environment = "empty"

[oracle]
tag = "yulang2-oracle"
tag_object = "<annotated tag object id>"
commit = "<peeled commit id>"
```

`case_count` は directory scan から検証または生成し、case の手書き index は置かない。
`schema_version` は TOML shape、`contract_version` は fixture の意味論を versioning する。
`corpus_revision` は同じ contract version 内で case set または record を更新したときに
上げる。`oracle` は oracle-anchored case を一件でも持つ corpus で必須とし、stable-core と
同じ provenance の考え方を使う。`defaults.syntax_environment` は将来の `parse_file` 呼び出し
に必要な test input profile であり、v0 の atomic fixture は `empty` を既定とする。ここで
`empty` は外部から import した dynamic operator がないことを表し、fixed grammar まで空に
する意味ではない。named profile の内容や syntax dependency planning は本 schema の対象外である。

case id は directory 名から得る。各 `fixture.toml` は次の logical section を持つ。

| section | 意味 |
| --- | --- |
| `case` | source file、説明、検索用 tag |
| `input` | `parse_file` に渡す syntax-environment profile の選択。省略時は corpus default |
| `boundary` | §18 の未決定事項に触れる case で、何を assert しないかを明記 |
| `header` | `scan_header` が返した ordered diagnostic key |
| `header.coverage` | `HeaderInfo` が観測した byte range と stop reason |
| `header.imports` | header phase が commit した import fact |
| `header.operators` | header phase が commit した operator fact |
| `full` | `ParsedFile::diagnostics()` の ordered diagnostic key |
| `full.header_projection` | full grammar が CST 上の共通 header 範囲から独立に得た fact |
| `full.recovery` | full CST の `Missing` / `Error` node の限定 projection |
| `diagnostics` | key から identity、内容、range、recovery site への定義 |
| `yulang2` | 任意の Yulang2 oracle anchor |

### HeaderInfo projection

`header.coverage` は次を持つ。

- `range`: scanner が header として観測した source prefix。先頭は常に `0`、終端は
  最初の non-header token の start offset または EOF とする。separator / newline を header
  scan が消費した場合は range に含める。
- `stop`: `eof` または `first_non_header`。最初の body statement は正常な
  `first_non_header` であり diagnostic ではない。

各 `header.imports` record は次を持つ。

- `key`: fixture 内だけで使う fact join key。production ID ではない。
- `range`: commit された import item の source range。
- `form`: `plain`、`mod`、`realm`、`band` の source-level form。
- `path`: resolution 前の path component の array。`ModuleId` は置かない。
- `visibility`: `private` または `public` の source-level visibility。
- `alias`: alias がある場合だけ置く。

group import は、共通 prefix を展開した後の、独立して完全かつ commit された item 一件を
一 record とする。不完全な item の placeholder fact は置かない。

各 `header.operators` record は `key`、operator header の `range`、`name`、`fixity`、
`visibility`、`binding_power` を持つ。`binding_power` は left / right のうち該当する side
だけを持つ inline table とし、full body の range や body の成否は含めない。この projection
は将来の `HeaderOperator` の Rust field layout を固定せず、§4.2.2 が parity 対象とする
operator shape だけを固定する。たとえば infix operator の record は
`binding_power = { left = 60, right = 61 }` のようになる。`fixity` の canonical spelling は
grammar の最小核と一緒に enum 化し、fixture 内では source spelling ではなくその enum 値を使う。

header fact は recovery node の有無から推測しない。fixture に record があることは、必須
field が一意に確定して transaction 的に commit されたことを意味する。record がないことは
空 fact の commit を意味しない。

`case.tags` に `late-use` または `non-header-mod` を持つ case は、次の boundary を明記しなければ
schema validation error とする。

```toml
[boundary]
header_info = "raw_observation_only"
semantic_dependency = "not_asserted"
source_set_expansion = "not_asserted"
note = "HeaderInfo の期待値は raw output だけを記録し、§18 の結論を表さない。"
```

この section は「semantic dependency ではない」という negative assertion ではない。
どちらの結論も fixture の比較対象に含めないという宣言である。

### Full-parse and recovery projection

`full.header_projection.imports` と `full.header_projection.operators` は、full grammar が
`header.coverage.range` 内の対応 declaration から得た fact を記録する。shape は header
側と同一で、同じ declaration には同じ `key` を使う。schema loader 自体が、同じ key の
header/full record について range、path / operator shape、visibility を比較し、異なる期待値を
持つ fixture を拒否する。両側の import key set と operator key set も完全一致を要求する。

将来の harness はこの full projection を `ParsedFile.header()` から読んではならない。それでは
同じ `Arc<HeaderInfo>` を二度比較するだけになる。full CST の対応 declaration、または full
grammar が公開する test-only typed projection から独立に作り、production caller が CST を
再走査して diagnostic を生成する経路にはしない。

各 `full.recovery` record は次を持つ。

- `key`: fixture-local recovery site key。
- `kind`: `missing` または `error`。
- `range`: recovery node が所有する byte range。
- `role`: CST kind numberではなく、`import_path`、`closing_delimiter` のような安定した
  grammar role。
- `expected`: `missing` の場合に必須の expected grammar element。
- `text`: `error` の場合に必須で、`main.yu[range]` と byte-for-byte で一致する text。
- `diagnostic`: 対応する diagnostic key。

schema validation で `missing` は `start == end`、`expected` あり、`text` なしを要求する。
`error` は `start < end`、`text` あり、`expected` なしを要求する。すべての recovery record と
diagnostic record は `diagnostic` / `recovery` で bijection を作る。これにより空の `Error`、
source byte を持つ `Missing`、silent recovery、同じ region の token ごとの重複 diagnostic を
fixture level で表現できないようにする。

full CST 全体の dump は記録しない。harness はすべての expected recovery node が一度ずつ存在し、
未記載の recovery node がないことに加え、CST が balanced で source token / trivia の byte を
順序通り一度ずつ保存することを全 case で無条件に検査する。この二つには false を期待する
field を用意しない。

### Diagnostic identity and merge

`header.diagnostics` と `full.diagnostics` は diagnostic key の ordered array である。
`full.diagnostics` は raw full-parser-only list ではなく、`ParsedFile::diagnostics()` が返す
header + body の exhaustive whole-file list を表す。各 key は `diagnostics` の一 record を参照する。

```toml
[[diagnostics]]
key = "header-missing-import-path"
id = { origin = "header", event = 0 }
code = "yulang.syntax"
severity = "error"
message = "expected import path"
primary = { start = 3, end = 3 }
recovery = "missing-import-path"
```

`key` は人が読み書きする join label であり、production `DiagnosticId` の文字列表現ではない。
`id.origin` は cause authority の `header` / `full`、`id.event` は source revision 内の
deterministic recovery event sequence である。production の `DiagnosticId` は opaque newtype の
ままでもよい。harness は header result で expected key に対応づいた実 ID を保持し、
`ParsedFile` の同じ key が値として同一の ID を持つことを比較する。message / range が同じ
別 ID を deduplicate したことにはしない。

schema と harness は次を検査する。

1. key、`id`、recovery link は case 内で unique である。
2. `header.diagnostics` は header-origin record と正確に一致する。
3. header の全 key と実 `DiagnosticId` は full list に同じ順序規則のもとで一度だけ現れる。
4. full-origin record は header list に現れず、full list には一度だけ現れる。
5. full list は `(primary.start, primary.end, id.event, code)` で決定的に並ぶ。
6. EOF `Missing` の primary range は `source.len()..source.len()` である。
7. recovery node と diagnostic は一対一で、drop、duplicate、unlisted record がない。

### Header/full parity policy

v0 は `parity = "known_divergent"` や expected-failure field を持たない。header/full の共通
fact は独立の section に明記するが、その expected record 自体が食い違う fixture は invalid、
実測値が食い違う parse は compiler invariant violation とする。full の値で header graph を
上書きして test を続けてはならない。

operator header は valid だが body が malformed、または import target は complete だが
無関係な末尾 token が malformed という case では、共通 fact は両 phase に残り、追加の
full-origin diagnostic だけが full list に加わる。これは parity failure ではない。一方、
target、operator name、fixity、binding power が確定しない declaration は、両 projection に
fact を置かない。

### Optional Yulang2 oracle anchor

Yulang2 の実 diagnostic に対応する case だけ、次の optional section を持てる。

```toml
[yulang2]
command = "check"
std = "none"

[[yulang2.diagnostics]]
key = "header-missing-import-path"
code = "yulang.syntax"
message = "<exact Yulang2 message>"
primary = { start = 3, end = 3 }
```

これは Yulang3 の phase product を Yulang2 が持っていたという主張ではなく、移行初期の
presentation adapter が保つ code、message、range の anchor である。採取時は corpus manifest
が指す `yulang2-oracle` tag の peeled commit から reference CLI を build し、case の
`main.yu` と byte-for-byte 同じ source、記録した `command` / `std` 条件で実行する。CLI の
diagnostic output を先に保存し、その code と exact message を転記し、primary span を同じ
UTF-8 byte range へ正規化する。Yulang3 の現在の出力から oracle record を逆生成しない。
raw capture と byte-range 変換の具体的な tool は、fixture population 前に一つへ決める。

### Worked example（illustrative only）

これは「header region の必須 import path が欠落し、その後の正常な header は発見される」
case の schema 使用例であり、今回追加する実 fixture ではない。診断文言と import syntax の
最終仕様も、この例では決定しない。

`main.yu`:

```yu
use
use std.data
my value = 1
```

`fixture.toml`:

```toml
[case]
source = "main.yu"
description = "missing header import path does not hide the following valid header"
tags = ["header-recovery", "missing", "header-full-parity"]

[input]
syntax_environment = "empty"

[header]
diagnostics = ["header-missing-import-path"]

[header.coverage]
range = { start = 0, end = 17 }
stop = "first_non_header"

[[header.imports]]
key = "std-data"
range = { start = 4, end = 16 }
form = "plain"
path = ["std", "data"]
visibility = "private"

[full]
diagnostics = ["header-missing-import-path"]

[[full.header_projection.imports]]
key = "std-data"
range = { start = 4, end = 16 }
form = "plain"
path = ["std", "data"]
visibility = "private"

[[full.recovery]]
key = "missing-import-path"
kind = "missing"
range = { start = 3, end = 3 }
role = "import_path"
expected = "path"
diagnostic = "header-missing-import-path"

[[diagnostics]]
key = "header-missing-import-path"
id = { origin = "header", event = 0 }
code = "yulang.syntax"
severity = "error"
message = "expected import path"
primary = { start = 3, end = 3 }
recovery = "missing-import-path"
```

この例では最初の不完全な `use` の fact は commit されず、二つ目だけが両 projection に
現れる。byte 3 の `Missing` は source を所有せず、header diagnostic の実 ID が final list に
一度だけ移る。body の先頭 byte 17 は header error ではなく正常な stop boundary である。

## Directory/file layout

population 後の配置は次の通りとする。

```text
tests/contracts/phase2-parser/v0/
  corpus.toml
  cases/
    <case-id>/
      main.yu
      fixture.toml
```

`phase2-parser` は stable-core と異なる contract family であり、
`tests/contracts/stable-core/v0/` の下には置かない。`v0` は Phase 2 の番号ではなく、この
schema semantics の contract version である。case category は `tags` で検索できるが、case
一覧を root manifest に重複して手書きしない。すべての parser case は phase expectation を
持つため、stable-core の「metadata が必要な case だけ sidecar」という原則に対し、この
family では `fixture.toml` が全 case で必須になる。

multi-module syntax-planning scenario や before/after edit scenario を追加するときは、scenario
directory から複数の atomic source snapshot を参照する。各 snapshot の header/full/recovery/
diagnostic assertion は本 schema を再利用し、`fixture.toml` に graph resolution や cache state
を混ぜない。

## Relationship to the existing stable-core corpus

再利用する convention は次の通りである。

- versioned contract family ごとの root `corpus.toml`。
- case ごとの source file と TOML sidecar。
- UTF-8 byte range。
- oracle tag object / peeled commit を含む provenance。
- directory scan を authority とし、manifest に case list を重複させない運用。

分けるものは次の通りである。

- stable-core は CLI / compiler の end-to-end output、phase2-parser は immutable phase output と
  parser invariant を固定する。
- stable-core の `diagnostic.toml` は final presentation の count / text / range を記録する。
  phase2-parser の `fixture.toml` は cause origin、event identity、header/full membership、
  recovery node との対応まで記録する。
- stable-core の stdout / stderr / public signature record を phase2-parser へ持ち込まない。
- phase2-parser の optional Yulang2 record は diagnostic presentation の anchor に限り、
  Yulang2 parser internals や full compiler behavior の snapshot として扱わない。

同じ source を両 corpus に置く必要が生じても、一方から他方を暗黙に参照しない。それぞれの
contract が読んだ byte を自己完結して保持し、必要なら provenance note で対応関係を示す。
これにより stable-core の freeze と Phase 2 schema の versioning を独立させる。

## Intended harness integration sketch

`yu-syntax` に parse API が生えた後の一 case の実行順は次の通りである。

1. `corpus.toml` と `fixture.toml` を deserialize し、range、key uniqueness、recovery/diagnostic
   bijection、§18 boundary、expected parity を実装非依存に schema validation する。
2. `main.yu` を byte-preserving に読み、`scan_header(source)` を一度呼ぶ。
3. coverage、committed imports / operators、ordered header diagnostics を typed projection で比較し、
   diagnostic key と実 `DiagnosticId` の対応を保持する。
4. `input.syntax_environment` profile から immutable test environment を取得し、同じ source と
   同じ `HeaderInfo` を `parse_file` に一度渡す。
5. full CST 由来の header projection を header 実測値と期待値の両方へ比較する。不一致時は
   ordinary assertion update や full-value overwrite ではなく invariant violation として fail する。
6. full CST の recovery node set、`Missing` / `Error` range rule、balance、source byte conservation
   を検査する。
7. `ParsedFile::diagnostics()` の exact ordered set を比較する。header-origin key については
   step 3 で保持した実 ID と同一であることを検査し、drop と duplicate を別々に報告する。
8. `yulang2` section がある場合は、Y3 presentation adapter の code / message / range を oracle
   record と比較する。通常の PR test で Yulang2 binary を毎回起動する必要はない。

fixture parser と schema validator は test-support 側に置き、production parser に TOML、fixture
key、oracle field の知識を入れない。full CST projection は test assertion のためだけに使い、
production diagnostic caller に CST 再走査を戻さない。

## Open questions/risks for Claude and the user to weigh in on

1. **`HeaderCoverage` の projection:** `range + stop` で十分か、opaque body scan の終端理由も
   public contract に必要か。population 前に `HeaderCoverage` の最小 public shape と照合する
   必要がある。
2. **operator binding-power shape:** left / right の optional field で全 fixity を正規化できるか。
   実 grammar が別の意味を持つ場合は、fixture population 前に semantic shape を直す必要がある。
3. **recovery `role` vocabulary:** raw CST kind に結合しないための field だが、自由文字列の typo を
   防ぐ enum は grammar の最小核と同時に確定する必要がある。
4. **`DiagnosticId` の test observability:** production ID を serialize する必要はないが、header と
   `ParsedFile` の値同一性、および deterministic event sequence を typed test API から観測できる
   必要がある。
5. **Yulang2 range capture:** reference CLI が byte span を直接出さない場合、raw line / column から
   byte range へ変換する単一 tool と、tab / Unicode の column rule を population 前に固定する必要が
   ある。
6. **syntax-environment profile:** `empty` で足りない imported-operator case が現れた時、named profile
   を本 family の support data に置くか、syntax-planning scenario だけで所有するかを決める必要が
   ある。atomic output schema はどちらでも変わらない。
7. **scenario composition:** syntax reexport cycle と body-only/header edit の incremental parity は
   atomic snapshot だけでは orchestration を表せない。graph / revision semantics を各担当設計で
   決め、ここへ ad hoc な cache field を足さないことが必要である。
8. **parity staging:** この draft は known-divergent escape hatch を拒否する。Phase 2 実装途中の
   workflow に一時的な選別が必要なら、contract data の期待値ではなく test target / worklist 側で
   管理する方針でよいか、レビューで確認したい。
