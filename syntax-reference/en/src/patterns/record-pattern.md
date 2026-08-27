# Record patterns

## 1. Status, authority, and last verification

The Authoritative RecordPattern addendum is at lines 8613–9312 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its separator rule is revised in place by the Authoritative layout addendum at 9314–9696, and ambient-owner recovery is revised by `ASOB-G` at 18358–19161. The closing signatures record review, confirmation, and user approval.

Implementation commits are `640cd1b4`, `81ef211d`, `f38c77d8`, and `0da2d26e`. This page was checked against `102cfa98`.

## 2. Scope and non-scope

A RecordPattern is a brace-delimited sequence of name-only fields and spreads. Empty records, shorthand fields, nested-pattern fields, defaults, trailing commas, layout-newline separators, unrestricted spread placement, typed recovery, and caller-close handoff are in scope.

Expression braces, record expression/type grammar, duplicate-field validation, spread matching semantics, typing, Pattern HIR/lowering, diagnostics wording, and formatter behavior are out of scope.

## 3. BNF-equivalent grammar

```text
RecordPattern := LBrace OpeningTrivia [ RecordPatternItem { RecordPatternSeparator RecordPatternItem } [ RecordPatternSeparator ] ] RBrace
RecordPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(record_pattern_base)
RecordPatternItem := RecordPatternField | RecordPatternSpreadItem
RecordPatternField := PatternFieldName [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ] | G0 Equals G* OperatorChain ]
PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
```

`G0` contains no physical newline. The base is captured after the opener: a following indentation at or below `record_pattern_base` makes a newline a separator; a deeper newline remains continuation. Semicolon is never a separator.

## 4. Judge, priority, and owner boundary

`{` selects RecordPattern only from the Pattern primary entry; expression `{...}` remains the expression owner. A field accepts only an identifier or sigil identifier. After that name, same-line exact `:` wins, then same-line exact `=`; otherwise it is shorthand. `==`, `=>`, and `=+` are never prefix-split as a default marker.

The field owner consumes its first colon before calling the nested Pattern, so `{a: A}` is a field form rather than an annotation. The RecordPattern consumes its own `}` first; a later outer colon may be a Pattern annotation. Record-local comma and close stops fence nested field Pattern/default parsing; propagated caller closes return without consumption. `ASOB-G` vetoes a local implicit newline for strict ambient dedent or an active If companion.

## 5. Byte-exact CST worked examples

The RecordPattern and layout addenda provide exact CST shapes, but no byte-range-annotated CST trees for these examples; no byte ranges are invented here.

```text
{a, width: local_width = 1, height = fallback, ..rest,}
```

Design lines 8900–8942 give the complete source-order tree: one `RecordPattern`, three `RecordPatternField` children, a `RecordPatternSpreadItem`, literal commas and whitespace, and nested `Pattern` / `OperatorChain` children. The final comma is raw trailing evidence.

```text
{a\nb}
```

Design line 8726 and recovery line 9176 classify a base-zero equal-indent newline as a valid separator between two shorthand fields, with no Missing node and no synthetic separator.

```text
{a\n  b}
```

Design lines 8727 and 9178 classify the deeper newline as continuation of the current field, not a second RecordPattern item.

```text
{a: = 1}
```

Design line 9187 preserves the colon field and records one missing nested Pattern; the same exact `=` is then owned as the optional default introducer.

## 6. Parser-side AST shape

`PatternPrimary::Record(RecordPattern)` stores `open`, recovered ordered `items`, literal `trailing_comma`, recovered `close`, and `range`. `RecordPatternItem` is `Field(RecordPatternField)` or `Spread(RecordPatternSpreadItem)`. A field uses `RecordPatternFieldForm::{Shorthand, Nested, Default}`; `Nested` stores its colon, recovered boxed Pattern, and optional `RecordPatternDefault`.

An accepted spread marker or default introducer remains represented when its mandatory RHS is incomplete. The AST preserves syntax-as-written rather than validating duplicate names or spread semantics.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `{}` / `{a,}` | valid empty/trailing-comma record; no Missing |
| `{,a}` / `{a,,b}` | one `PatternRole::RecordItem` Missing per absent item, then item retry |
| `{1,a}` / `{@ a}` | non-empty field/item Error; a valid field can retry |
| `{a b}` | one missing delimited separator before `b`, then same-position retry |
| `{a:}` / `{a:, b}` | one `PatternRole::RecordNestedPattern` Missing; close/comma stays owned |
| `{a: = 1}` | missing nested Pattern, then the same exact `=` starts the default |
| `{a =}` / `{a: p =}` | retain `Equals`; one `PatternRole::RecordDefaultExpression` Missing |
| `{..}` / `{..,a}` | preserve spread node; one missing spread RHS; comma/close remains owned |
| `{...a}` | malformed item Error, without splitting `...` into `DotDot` |
| missing/mismatched `}` | one record closing Missing/Error; caller safe point remains non-consuming |

The contract is one committed recovery node and one record per cause; malformed recovery stops before closes, separators, safe points, and retry candidates, avoiding a second same-cause Missing.

## 8. Boundary and state-restoration contract

The brace frame captures opening-trivia layout base once and restores delimiter, stop, layout, line/scanner, and sink state on normal close, recovery, and terminal exits. Direct and AST coverage includes nested records, missing/mismatched closes, case-arm arrows, layout boundaries, propagated right closes, and the `ASOB-G` ambient/If veto. The cross-cutting contract restores ambient/If, indentation, expression/type owner, ML state, and positional fence as well.

## 9. Yulang2 divergences

Yulang3 preserves name-only field heads (including sigils), field/default/spread forms, and layout-separated records. It keeps layout newlines as literal trivia instead of Yulang2 empty `Separator` nodes and uses typed Missing/Error with same-position retry instead of generic invalid-token recovery. Duplicate names and multiple/middle spreads remain parser-valid rather than becoming parse-time errors.

## 10. Known residual / deferred surface

`ASOB-G` documents residual hidden-boundary cases behind a missing nested delimiter when neither strict dedent nor an active If companion claims the gap. They remain characterized rather than silently passed. The Cast addendum separately characterizes its RecordPattern-containing residuals.

Deferred work includes duplicate-field/spread validation, matching/capture semantics, type checking, Pattern HIR/lowering, diagnostics text, and formatter policy.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/pattern.rs`: `parse_record_pattern`, `parse_record_item_ast`, `parse_record_default_ast`, `commit_direct_record_pattern`, `commit_direct_record_item`, `commit_direct_record_default`, `commit_direct_record_default_after_equals`, `commit_direct_pattern_delimited_items`, and `outer_pattern_close_stop_pending`.

Primary fixtures are `record_patterns_keep_field_forms_spreads_layout_and_recovery_local`, `ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`, `pattern_delimited_malformed_recovery_returns_the_same_ambient_gap`, and `pattern_caller_close_propagation_is_right_close_only`.
