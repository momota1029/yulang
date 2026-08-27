# Named-record types

## 1. Status, authority, and last verification

The Authoritative NamedRecordType addendum is lines 12867–13429 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its current ambient-owner behavior is also covered by `ASOB-G` at 18358–19161 and its shared malformed-trivia behavior by `TMN` and the positional fence at 16557–17289.

Implementation commits are `da50836b`, `68b3bac4`, `b906428f`, `d99d49e7`, `72948621`, `42c1544c`, and `2c4d7540`. This page was checked against `5df7ace1`.

## 2. Scope and non-scope

NamedRecordType adds `{a: A, b: B}` as a TypePrimary. Fields are plain identifier plus mandatory colon and canonical full TypeExpression RHS, separated by comma or qualifying layout newline.

It excludes record-pattern fields, expression records, shorthand/default/spread fields, sigil/numeric/path-qualified names, semicolon separators, declaration use-site wiring, typing, HIR/lowering, diagnostics text, and formatting.

## 3. BNF-equivalent grammar

```text
TypePrimary := TypeAtom | ParenthesizedTypeGroup | NamedRecordType
NamedRecordType := LBrace OpeningTrivia [ TypeRecordField { RecordTypeSeparator TypeRecordField } [ RecordTypeSeparator ] ] RBrace
TypeRecordField := Identifier TypeRecordFieldTrivia Colon TypeRecordFieldTrivia TypeExpression
RecordTypeSeparator := CommaBoundary | ImplicitNewlineBoundary(named_record_base)
TypeRecordFieldTrivia := EmptyTrivia | SameLineTrivia | TriviaWithDeeperFollowingIndent(named_record_base)
```

Opening trivia captures the layout base once. Equal-or-shallower newline returns to record separator judgment; deeper newline remains field RHS continuation.

## 4. Judge, priority, and owner boundary

At a required TypePrimary position, exact `{` is a NamedRecordType candidate after active stops/closes and ordinary atom/group candidates. After acceptance it cuts: malformed fields or close never become expression braces or another future primary. `F {a: A}` is a `TypeApplyArgument`; adjacent `F{a: A}` has no hidden apply authority.

Within a field, only a plain identifier can start field authority. The record owns field colon, comma, close, and layout. Before an RHS would accept a whitespace TypeApply, `named_record_next_field_candidate` detects a complete following `Identifier ... Colon` head: it returns the gap for one missing record separator rather than swallowing it as an apply. Ordinary `F B` remains a valid RHS apply.

## 5. Byte-exact CST worked examples

The addendum provides complete CST trees but no byte-range-annotated trees; no ranges are invented here.

```text
{a: A, b: List(Int)}
```

Design lines 13097–13125 show `TypeExpression > NamedRecordType` with two `TypeRecordField` children, raw comma/whitespace, and a nested `TypeCallTail` in the second RHS.

```text
{
  a: A
  b: B
}
```

Design lines 13127–13158 show opening, inter-field, and trailing newline/indentation as literal children of `NamedRecordType`; no empty `Separator` or synthetic comma appears.

```text
F {a: A}
```

Design lines 12990–12996 classify this as one `TypeApplyArgument` whose primary is `NamedRecordType`; the contrasting adjacent `F{a: A}` is returned to the caller.

## 6. Parser-side AST shape

`TypePrimary::Record(NamedRecordType)` stores `open`, recovered ordered `fields`, literal `trailing_comma`, recovered `close`, and `range`. `TypeRecordField` stores recovered `name`, `colon`, recovered boxed `type_expr`, and `range`.

After field authority is accepted, an incomplete internal slot remains a complete field with only that slot incomplete. A wholly absent field is a sequence-level incomplete field entry. This keeps name, colon, type, and close recovery cardinality distinct.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `{}` / valid comma or layout sequence | valid record; no recovery |
| leading/repeated comma | one `TypeRole::RecordField` Missing per absent field |
| same-line complete next field head | one `TypeRole::RecordFieldSeparator` Missing, then same-position field retry |
| semicolon between fields | non-empty separator Error; semicolon is not valid locally |
| missing/mismatched `}` | one NamedRecord closing Missing/Error; outer-owned close is not consumed |
| `{: A}` / `{@: A}` | one missing/error `TypeRole::RecordFieldName`, then same field continues |
| `{a A}` / malformed colon | one `TypeRole::RecordFieldColon` Missing/Error; type retries without cascade |
| accepted colon with missing/malformed RHS | one `TypeRole::RecordFieldType` Missing/Error; boundary remains owned |
| `{..Type}` / shorthand/default | whole-field or colon-role recovery; no spread/shorthand/default node |

Safe points include record comma, matching close, outer close/stop, qualifying newline, and field/slot retry candidates. One recovery node equals one committed record.

## 8. Boundary and state-restoration contract

The record frame captures opening layout, delimiter, stop, and `TypeDelimitedOwner::NamedRecord` state and restores it on normal, recovery, and rollback exits. AST/direct paths share field-authority and safe-point probes. `ASOB-G`, `TMN`, and positional-fence coverage preserve active If, ambient boundary, indentation, type-owner, and caller-boundary state.

## 9. Yulang2 divergences

Yulang3 retains mandatory colon, no shorthand/spread, empty/trailing-comma records, and comma-only explicit separators. It retains literal newline trivia instead of empty `Separator` nodes, requires non-empty trivia for record ML application, and replaces generic `TypeRecord`/`InvalidToken` behavior with typed field slots and same-position retry.

## 10. Known residual / deferred surface

The general hidden-boundary residual is documented by `ASOB-G`; no NamedRecord-specific exception broadens it. Deferred surfaces are field semantics, type checking, HIR/lowering, resolver/inference integration, diagnostics, formatting, and declaration use-site wiring.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_named_record_type`, `parse_type_record_field`, `commit_direct_named_record_type`, `commit_direct_type_record_field`, `named_record_next_field_candidate`, `classify_named_record_recovery`, `record_field_head_candidate`, `scan_record_invalid_run`, and `consume_record_colon_invalid_run`.

Fixtures include `named_record_types_are_primary_fields_with_comma_or_newline_boundaries`, `named_record_field_head_yields_before_type_apply`, `named_record_missing_name_commits_the_field_owner`, `named_record_malformed_field_boundary_does_not_cascade`, `named_record_rejects_spread_shorthand_and_default_field_forms`, `named_record_recovers_malformed_colon_and_type_slots`, `named_record_comma_policy_and_close_recovery_are_typed`, and `named_record_sequence_classifies_recovery_gaps_before_consuming_them`.
