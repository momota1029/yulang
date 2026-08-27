# Standalone `cast` declaration

## 1. Status, authority, and last verification

This page summarizes the Authoritative standalone cast-declaration addendum,
lines 21646–22774 of
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`: `CAST-G`,
`CAST-J`, `CAST-T`, and `CAST-R`. Its closing signature records eleven
independent review rounds before confirmation and user approval.

The thirteen implementation slices landed in `3d7154eb`, `003cdc9a`,
`bd96837d`, `d3778e13`, `0da2d26e`, `43abd938`, `fe67f4eb`, `f79df17f`,
`b6b4f5ba`, `0c5c4af9`, `e3cffdf1`, `372af45e`, and `dd1505f4`.
Gate 3b found and fixed a composition gap with the narrow opt-in
`recovered_primary_tail_stops` policy: an error-recovered nested Pattern
close could otherwise let the outer Pattern consume Cast's target colon. This
page was checked against `a00b8c74`.

## 2. Scope and non-scope

A standalone Cast is a root Declaration and nested Statement with optional
visibility, one parenthesized canonical Pattern, a mandatory colon and full
TypeExpression target, and either a bodyless semicolon or an exact-equals
inline/strictly-deeper indented body.

The addendum covers typed recovery, AST/direct-CST parity, shared root/nested
dispatch, and source-leading header discovery stopping without a fact. It does
not perform rule registration, source/target extraction, conversion
application, semantic validation, or downstream lowering and analysis.

## 3. BNF-equivalent grammar

```text
CastDeclaration := [ VisibilityKw Gcast+ ] CastKw Gcast-pattern CastPatternGroup Gcast-target CastTarget Gcast-form CastForm
CastPatternGroup := RecoveredLParen(Cast::PatternIntroducer) Gcast-delimited* RequiredPatternWithPolicy(Cast::Pattern) Gcast-delimited* RecoveredRParen(CastPattern)
CastTarget := RecoveredTargetColon(Cast::TargetIntroducer) Gcast-type RequiredTypeExpression(Cast::TargetType)
CastForm := BodylessSemicolon | DefinitionEquals CastDefinitionBody
CastDefinitionBody := Gcast-inline RequiredOperatorChain(Cast::Body) | IndentedStatementBlock(item-role := Cast::IndentedStatement)
VisibilityKw := MyKw | OurKw | PubKw
CastKw := exact maximal word "cast"
```

`Gcast-indent` is strictly-deeper continuation trivia and is owned by the
opening prefix of the existing `IndentedStatementBlock`. The Pattern policy
uses `Colon | Equal` only before a primary is accepted; ordinary Pattern
annotation and nested syntax retain their own authority after acceptance.

## 4. Judge, priority, and owner boundary

Only a statement-position exact contextual `cast`, bare or preceded by
`my`, `our`, or `pub` plus declaration-continuing trivia, is a Cast intro.
`casting`, `castaway`, and non-intro word positions are not split. Real intro
recognition is ordered after Impl and before Binding.

The Cast group owns exactly one canonical Pattern, not a ParenthesizedPattern
tuple/list wrapper. An actual `(` alone creates the Cast-local delimiter frame;
a missing opener never manufactures one. The delimiter-stack top distinguishes
the Cast-local `)` from outer-owned or unowned `)` bytes, which remain
non-consuming boundaries. A target colon owns a full TypeExpression episode
with scoped outer `Equal`, `Semicolon`, and conditional `Newline` stops.

An exact `;` cuts to the bodyless form. An exact `=` cuts to the definition
form; its one post-equals trivia run chooses either an inline `OperatorChain`
or an existing strictly-deeper indented statement block. A brace following an
inline expression is not a Cast body opener.

## 5. Byte-exact CST worked examples

The addendum supplies the following source-and-range trees directly.

```text
cast(x: A): B;
```

Design lines 22139–22163 give `CastDeclaration 0..14`, with
`CastPattern 4..10`, `Pattern 5..9`, `CastTarget 10..13`, and the
Cast-owned `Semicolon 13..14`.

```text
pub cast(x: A): B = x
```

Design lines 22165–22189 give `CastDeclaration 0..21`,
`CastPattern 8..14`, `CastTarget 14..17`, `Equals 18..19`,
`CastBody 19..21`, and its inline `OperatorChain 20..21`.

```text
pub cast(x: int): user_id = user_id { raw: x }
```

Design lines 22192–22234 give `CastDeclaration 0..46`, `CastBody 27..46`,
and inline `OperatorChain 28..46`. Its `MlArgument 36..46` contains the
ordinary `BracedStatementBlockExpression 36..46`; the brace is therefore
owned by the inline expression, not by Cast form selection.

```text
cast(x: A): B =
  x
```

Design lines 22240–22259 give `CastDeclaration 0..19`, `Equals 14..15`,
`CastBody 15..19`, and `IndentedStatementBlock 15..19`. The block's first
child is `Trivia 15..18`, followed by `Statement 18..19`; opening trivia is
inside the block range rather than a sibling owned by `CastBody`.

## 6. Parser-side AST shape

`CastDeclaration` stores `visibility`, recovered `pattern`, recovered
`target`, recovered `form`, and its source range. `CastPattern` stores
recovered `open`, one recovered boxed `Pattern` value, recovered `close`, and
its range. `CastTarget` similarly stores a recovered colon, one recovered
boxed `TypeExpression`, and its range.

`CastForm` is either `Bodyless { semicolon }` or `Definition { equals, body, range }`; `CastBody` is `Inline { expression: OperatorChain }` or `Indented { block: IndentedStatementBlock }`. These are the actual types in
`crates/yu-syntax/src/grammar/declaration.rs`; no `BindingBody` or synthetic
separator is substituted.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| exact intro at EOF/owner boundary | one `Missing(CastRole::PatternIntroducer)`; downstream slots do not cascade |
| missing/malformed opener | one `CastRole::PatternIntroducer` Missing/Error, then same-position Pattern retry or punctuation/boundary handoff |
| mandatory Pattern failure | nested Pattern recovery retains its own role; a valid retry completes the same slot |
| Cast-local vs outer `)` | only the actual Cast-local current-top close is consumed; outer/unowned closes are non-consuming |
| missing/malformed close | one closing-delimiter Missing/Error, with target-colon same-position retry when evidence exists |
| missing/malformed target colon | one `CastRole::TargetIntroducer` Missing/Error, then same-position TypeExpression or form-starter retry |
| target TypeExpression failure | nested Type recovery and same-slot retry; `=`/`;` or an outer boundary remains available to form/owner |
| missing/malformed form starter | one `CastRole::BodyIntroducer` Missing/Error; actual `;` or `=` retries the form |
| missing/malformed body | one `CastRole::Body` Missing/Error; indented item failures stay `CastRole::IndentedStatement` |

The governing invariants are one accepted Cast per declaration node, one
recovery range per recovery node and committed record, and no same-cause
downstream Missing cascade. Nested Pattern, TypeExpression, and Expression
recovery is neither relabelled nor duplicated as Cast recovery.

## 8. Boundary and state-restoration contract

Before promotion, Gate 7 checked the isolated adapter at root, indented,
braced, and inline ambient boundaries, with depth-2+ ambient/If state, every
fixed terminal boundary, local and outer parentheses, and normal/recovery/
rollback exits. It requires exact restoration of input/line/sink, ambient/If,
delimiter/stop, indentation, Pattern layout, expression-type owner, ML,
positional fence, and TypeExpression episode depth.

Gate 8 repeated that contract through real root and canonical-statement
dispatch, including Cast indented bodies containing expressions and supported
statement/declaration kinds. Gate 3b's opt-in tail-stop repair leaves callers
that do not opt in unchanged.

## 9. Yulang2 divergences

Surface spelling follows the `yulang2-oracle` parser: optional visibility,
one Pattern group, colon plus full target type, and semicolon or equals body.
Contextual-word handling is parity rather than divergence: `cast` remains an
ordinary identifier outside declaration-intro positions.

Yulang3 deliberately replaces Yulang2 generic invalid tokens and silent-close
behavior with typed roles, same-slot retry, exact ownership, and no-cascade
recovery. It also preserves the inline constructor-brace interpretation and
does not add a brace/colon Cast declaration body or punctuation-free
target/body split.

## 10. Known residual / deferred surface

The documented residual is condition-based, not a closed table. It applies
only when all four conditions hold: a missing-close nested Pattern or
TypeExpression owner is actively recovering or judging a post-item boundary;
the gap is an enclosing sequence's next-candidate boundary; that boundary is
not visible as caller-owned; and the inner driver has a real path to consume or
reinterpret it as local recovery/separation and continue with the next outer
candidate. This includes clean local `ImplicitNewline` continuation after a
complete item, not only malformed scans.

`cast_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners` fixes
the current AST/direct remainder, recovery, discovery count, and lossless CST
for six non-exhaustive characterizations: ListPattern/CatchBraced,
ParenthesizedPattern/CatchIndented, RecordPattern/root same-indent,
Pattern-annotation EffectRow/CaseIndented, CastTarget EffectRow/root
same-indent, and ListPattern/CaseInline comma. They are not green success
cases; well-delimited input, propagated caller closes, strict dedent, active
If companions, and visible caller boundaries remain required success cases.

Deferred surfaces include Cast-specific `via`, cast-rule registration,
implicit conversion application, expected-type behavior, ambiguity/coherence,
and HIR, resolver, inference, monomorphization, diagnostics wording, and
formatter work. The explicit `.cast` method/role family remains separate.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`, the Cast path is implemented
by `recognize_cast_statement_intro`,
`parse_required_cast_pattern_value_isolated`,
`commit_required_cast_pattern_value_isolated`,
`parse_required_cast_target_type_isolated`,
`commit_required_cast_target_type_isolated`, `parse_cast_pattern_isolated`,
`commit_cast_pattern_isolated`, `parse_cast_target_isolated`,
`commit_cast_target_isolated`, `parse_cast_declaration_form_aware_isolated`,
`commit_cast_declaration_isolated`, `parse_cast_form_isolated`, and
`commit_cast_form_isolated`.

Regression fixtures include
`cast_statement_intro_is_exact_isolated_and_rolls_back_every_probe_state`,
`isolated_cast_signature_prefix_lattice_is_typed_lossless_and_ast_direct_exact`,
`isolated_cast_form_uses_the_neutral_binding_style_layout_without_binding_identity`,
`isolated_cast_declaration_direct_cst_is_byte_exact_and_matches_ast_forms`,
`isolated_cast_declaration_recovery_rows_are_typed_non_cascading_and_lossless`,
`isolated_cast_declaration_restores_full_boundary_state_before_promotion`,
`cast_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners`, and
`cast_gate_9_final_public_boundary_matrix_closes_scope_and_parity`.
