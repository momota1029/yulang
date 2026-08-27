# Named-record type

## 1. 状態・正本・最終確認

Authoritative な NamedRecordType 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 12867–13429 行にある。current ambient-owner behavior は 18358–19161 行の `ASOB-G`、shared malformed-trivia behavior は 16557–17289 行の `TMN` と positional fence にも従う。

実装 commit は `da50836b`、`68b3bac4`、`b906428f`、`d99d49e7`、`72948621`、`42c1544c`、`2c4d7540`。このページは `5df7ace1` を基準に確認した。

## 2. 対象範囲と非対象

NamedRecordType は `{a: A, b: B}` を TypePrimary として追加する。field は plain identifier、mandatory colon、canonical full TypeExpression RHS だけで、comma または qualifying layout newline で区切る。

record-pattern field、expression record、shorthand/default/spread field、sigil/numeric/path-qualified name、semicolon separator、declaration use-site wiring、typing、HIR/lowering、diagnostics text、formatting は対象外である。

## 3. BNF 相当の grammar

```text
TypePrimary := TypeAtom | ParenthesizedTypeGroup | NamedRecordType
NamedRecordType := LBrace OpeningTrivia [ TypeRecordField { RecordTypeSeparator TypeRecordField } [ RecordTypeSeparator ] ] RBrace
TypeRecordField := Identifier TypeRecordFieldTrivia Colon TypeRecordFieldTrivia TypeExpression
RecordTypeSeparator := CommaBoundary | ImplicitNewlineBoundary(named_record_base)
TypeRecordFieldTrivia := EmptyTrivia | SameLineTrivia | TriviaWithDeeperFollowingIndent(named_record_base)
```

Opening trivia が layout base を一度 capture する。equal-or-shallower newline は record separator judge へ戻り、deeper newline は field RHS continuation になる。

## 4. Judge・priority・owner boundary

required TypePrimary position では active stop/close と ordinary atom/group candidate の後に exact `{` を NamedRecordType candidate として判定する。accept 後は cut し、malformed field/close でも expression brace や future primary に reinterpret しない。`F {a: A}` は `TypeApplyArgument`、adjacent `F{a: A}` は hidden apply authority を持たない。

field 内では plain identifier だけが field authority を開始する。record は field colon、comma、close、layout を own する。RHS が whitespace TypeApply を accept する前に `named_record_next_field_candidate` が complete `Identifier ... Colon` head を検出し、一件の missing record separator として gap を返す。ordinary `F B` は valid RHS apply のまま残る。

## 5. Byte-exact CST の worked examples

追補には complete CST tree があるが byte-range 付き tree はない。ここでは range を作らない。

```text
{a: A, b: List(Int)}
```

設計文書 13097–13125 行は、二つの `TypeRecordField`、raw comma/whitespace、二つ目の RHS にある nested `TypeCallTail` を持つ `TypeExpression > NamedRecordType` を示す。

```text
{
  a: A
  b: B
}
```

設計文書 13127–13158 行は opening/inter-field/trailing newline と indentation を `NamedRecordType` の literal child として示す。empty `Separator` も synthetic comma も作らない。

```text
F {a: A}
```

設計文書 12990–12996 行は、primary が `NamedRecordType` の `TypeApplyArgument` 一件として分類する。対照的な adjacent `F{a: A}` は caller へ返す。

## 6. Parser 側 AST shape

`TypePrimary::Record(NamedRecordType)` は `open`、recovered ordered `fields`、literal `trailing_comma`、recovered `close`、`range` を持つ。`TypeRecordField` は recovered `name`、`colon`、recovered boxed `type_expr`、`range` を持つ。

field authority の accept 後は internal slot だけが incomplete になり、wholly absent field は sequence-level incomplete field entry になる。これにより name/colon/type/close recovery cardinality を分ける。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `{}` / valid comma/layout sequence | valid record。recovery なし |
| leading/repeated comma | absent field ごとに `TypeRole::RecordField` Missing 一件 |
| same-line complete next field head | `TypeRole::RecordFieldSeparator` Missing 一件後 same-position field retry |
| semicolon between fields | non-empty separator Error。local separator ではない |
| missing/mismatched `}` | NamedRecord closing Missing/Error 一件。outer-owned close は consume しない |
| `{: A}` / `{@: A}` | missing/error `TypeRole::RecordFieldName` 一件後 same field 継続 |
| `{a A}` / malformed colon | `TypeRole::RecordFieldColon` Missing/Error 一件。cascade せず type retry |
| accepted colon の missing/malformed RHS | `TypeRole::RecordFieldType` Missing/Error 一件。boundary は owner のまま |
| `{..Type}` / shorthand/default | whole-field または colon-role recovery。spread/shorthand/default node なし |

safe point は record comma、matching close、outer close/stop、qualifying newline、field/slot retry candidate を含む。recovery node 一つは committed record 一つに対応する。

## 8. Boundary と state-restoration contract

record frame は opening layout、delimiter、stop、`TypeDelimitedOwner::NamedRecord` state を capture し、normal/recovery/rollback exit で復元する。AST/direct は field-authority/safe-point probe を共有する。`ASOB-G`、`TMN`、positional-fence coverage は active If、ambient boundary、indentation、type-owner、caller-boundary state を保つ。

## 9. Yulang2 divergences

Yulang3 は mandatory colon、no shorthand/spread、empty/trailing-comma record、comma-only explicit separator を保つ。empty `Separator` node の代わりに literal newline trivia を残し、record ML application に non-empty trivia を要求し、generic `TypeRecord`/`InvalidToken` behavior を typed field slot と same-position retry に置換する。

## 10. Known residual / deferred surface

general hidden-boundary residual は `ASOB-G` が記録し、NamedRecord-specific exception で広げない。field semantics、type checking、HIR/lowering、resolver/inference integration、diagnostics、formatting、declaration use-site wiring は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_named_record_type`、`parse_type_record_field`、`commit_direct_named_record_type`、`commit_direct_type_record_field`、`named_record_next_field_candidate`、`classify_named_record_recovery`、`record_field_head_candidate`、`scan_record_invalid_run`、`consume_record_colon_invalid_run` を参照する。

fixture は `named_record_types_are_primary_fields_with_comma_or_newline_boundaries`、`named_record_field_head_yields_before_type_apply`、`named_record_missing_name_commits_the_field_owner`、`named_record_malformed_field_boundary_does_not_cascade`、`named_record_rejects_spread_shorthand_and_default_field_forms`、`named_record_recovers_malformed_colon_and_type_slots`、`named_record_comma_policy_and_close_recovery_are_typed`、`named_record_sequence_classifies_recovery_gaps_before_consuming_them`。
