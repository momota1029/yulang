# Record pattern

## 1. 状態・正本・最終確認

Authoritative な RecordPattern 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 8613–9312 行にある。separator 規則は 9314–9696 行の Authoritative layout 追補で in-place 更新され、ambient owner recovery は 18358–19161 行の `ASOB-G` で更新される。各追補の末尾署名は査読・確定・ユーザ承認を記録している。

実装 commit は `640cd1b4`、`81ef211d`、`f38c77d8`、`0da2d26e`。このページは `102cfa98` を基準に確認した。

## 2. 対象範囲と非対象

RecordPattern は brace で区切られた name-only field と spread の列である。empty record、shorthand field、nested Pattern field、default、trailing comma、layout newline separator、任意位置・個数の spread、typed recovery、caller-close handoff を対象にする。

expression の brace、record expression/type grammar、duplicate-field validation、spread matching semantics、typing、Pattern HIR/lowering、diagnostics 文言、formatter は対象外である。

## 3. BNF 相当の grammar

```text
RecordPattern := LBrace OpeningTrivia [ RecordPatternItem { RecordPatternSeparator RecordPatternItem } [ RecordPatternSeparator ] ] RBrace
RecordPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(record_pattern_base)
RecordPatternItem := RecordPatternField | RecordPatternSpreadItem
RecordPatternField := PatternFieldName [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ] | G0 Equals G* OperatorChain ]
PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
```

base は opener 後に capture する。following indentation が `record_pattern_base` 以下の newline は separator、より深い newline は continuation になる。semicolon は separator ではない。`G0` は physical newline を含まない。

## 4. Judge・priority・owner boundary

`{` は Pattern primary entry からだけ RecordPattern を選ぶ。expression の `{...}` は expression owner のまま残る。field head は identifier または sigil identifier に限る。name 後は same-line の exact `:`、次に same-line の exact `=`、それ以外は shorthand を選ぶ。`==`、`=>`、`=+` は default marker に prefix split しない。

field owner は nested Pattern を呼ぶ前に first colon を consume するため、`{a: A}` は annotation ではなく field form になる。RecordPattern は own `}` を先に consume し、その後の outer colon は Pattern annotation になり得る。record-local comma/close stop は nested field Pattern/default を fence し、propagated caller close は non-consuming で返す。`ASOB-G` は strict ambient dedent または active If companion で local implicit newline を veto する。

## 5. Byte-exact CST の worked examples

RecordPattern と layout の追補には exact CST shape はあるが、この例群の byte-range 付き CST tree はない。ここでは byte range を作らない。

```text
{a, width: local_width = 1, height = fallback, ..rest,}
```

設計文書 8900–8942 行は source-order tree 全体を示す。`RecordPattern` 一個、三つの `RecordPatternField`、一つの `RecordPatternSpreadItem`、literal comma/whitespace、nested `Pattern` / `OperatorChain` が入り、最後の comma は raw trailing evidence である。

```text
{a\nb}
```

設計文書 8726 行と recovery 表 9176 行は、base zero の equal-indent newline を二つの shorthand field 間の valid separator とし、Missing node も synthetic separator も置かない。

```text
{a\n  b}
```

設計文書 8727 行と 9178 行は、deeper newline を current field の continuation とし、二つ目の RecordPattern item にしない。

```text
{a: = 1}
```

設計文書 9187 行は colon field を保持して nested Pattern を一件 Missing にし、同じ exact `=` を optional default introducer として所有する。

## 6. Parser 側 AST shape

`PatternPrimary::Record(RecordPattern)` は `open`、recovered ordered `items`、literal `trailing_comma`、recovered `close`、`range` を持つ。`RecordPatternItem` は `Field(RecordPatternField)` または `Spread(RecordPatternSpreadItem)` である。field は `RecordPatternFieldForm::{Shorthand, Nested, Default}` を使い、`Nested` は colon、recovered boxed Pattern、optional `RecordPatternDefault` を持つ。

accepted spread marker や default introducer は mandatory RHS が incomplete でも残る。AST は duplicate name や spread semantics を validation せず syntax-as-written を保存する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `{}` / `{a,}` | valid empty/trailing-comma record。Missing なし |
| `{,a}` / `{a,,b}` | absent item ごとに `PatternRole::RecordItem` Missing 一件、その後 item retry |
| `{1,a}` / `{@ a}` | non-empty field/item Error。valid field は retry できる |
| `{a b}` | `b` 前に missing delimited separator 一件、same-position retry |
| `{a:}` / `{a:, b}` | `PatternRole::RecordNestedPattern` Missing 一件。close/comma は owner のまま |
| `{a: = 1}` | nested Pattern Missing 後、同じ exact `=` が default を開始 |
| `{a =}` / `{a: p =}` | `Equals` を保持し `PatternRole::RecordDefaultExpression` Missing 一件 |
| `{..}` / `{..,a}` | spread node を保持し missing spread RHS 一件。comma/close は owner のまま |
| `{...a}` | `...` を `DotDot` に split しない malformed item Error |
| missing/mismatched `}` | record closing Missing/Error 一件。caller safe point は non-consuming |

契約は cause ごとに committed recovery node と record を一つだけ作る。malformed recovery は close、separator、safe point、retry candidate の前で止まり、same-cause の二件目 Missing を避ける。

## 8. Boundary と state-restoration contract

brace frame は opener trivia の layout base を一度 capture し、normal close、recovery、terminal exit のすべてで delimiter、stop、layout、line/scanner、sink state を復元する。AST/direct の fixture は nested record、missing/mismatched close、case-arm arrow、layout boundary、propagated right close、`ASOB-G` の ambient/If veto を含む。cross-cutting contract は ambient/If、indentation、expression/type owner、ML state、positional fence も復元する。

## 9. Yulang2 divergences

Yulang3 は name-only field head（sigil を含む）、field/default/spread form、layout-separated record を保つ。layout newline は Yulang2 の empty `Separator` node ではなく literal trivia として残し、generic invalid-token recovery ではなく typed Missing/Error と same-position retry を使う。duplicate name と multiple/middle spread は parse-time error にせず parser-valid のままにする。

## 10. Known residual / deferred surface

`ASOB-G` は missing nested delimiter の背後にある hidden boundary で、strict dedent も active If companion も gap を claim しない residual case を記録する。これらを黙って success と扱わない。Cast 追補は RecordPattern を含む別の residual を条件付きで記録する。

duplicate-field/spread validation、matching/capture semantics、type checking、Pattern HIR/lowering、diagnostics text、formatter policy は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/pattern.rs` では `parse_record_pattern`、`parse_record_item_ast`、`parse_record_default_ast`、`commit_direct_record_pattern`、`commit_direct_record_item`、`commit_direct_record_default`、`commit_direct_record_default_after_equals`、`commit_direct_pattern_delimited_items`、`outer_pattern_close_stop_pending` を参照する。

主な fixture は `record_patterns_keep_field_forms_spreads_layout_and_recovery_local`、`ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`、`pattern_delimited_malformed_recovery_returns_the_same_ambient_gap`、`pattern_caller_close_propagation_is_right_close_only`。
