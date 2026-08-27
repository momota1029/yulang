# Shared `derives` clause attachment

## 1. Status, authority, and last verification

This page summarizes the Authoritative shared derives addendum in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, lines 20278–21010:
`DRV-G`, `DRV-J`, `DRV-T`, and `DRV-R`.

The nine gates are represented by `919766cf`, `8ace7256`, `47a63de3`,
`695523ca`, `b6c9a391`, `9a6ab93e`, `2cd4a1e7`, `e00f9a6b`, `69589b5d`, and
`a3174886`; Gate 1 is split into neutral 1a/consumer 1b commits. `919766cf`
documents the reusable neutral TypeExpression episode infrastructure later used
by the impl and cast addenda. This page was checked against `d90b79b8`.

## 2. Scope and non-scope

A shared `DerivesClause` attaches in Struct header/trailing positions and Type
header/trailing-equality positions. It owns exact `derives`, one or more
TypeExpression role references, literal commas, and optional `via Identifier`.

It does not create a declaration, statement intro, delimiter owner, implicit
separator, role resolver, derive plan, generated impl, field lookup, or semantic
diagnostic.

## 3. BNF-equivalent grammar

```text
DerivesClause :=
    DerivesKw DerivesRoleTrivia RequiredTypeExpression(Derives::RoleReference)
    { DerivesRoleGap Comma DerivesRoleTrivia RequiredTypeExpression(Derives::RoleReference) }
    [ DerivesRoleGap ViaKw DerivesViaTrivia RequiredRawIdentifier(Derives::ViaTarget) ]
DerivesKw := exact contextual word "derives"
ViaKw := exact contextual word "via" inside an accepted DerivesClause
```

Attachments use qualifying same-line or strictly-deeper trivia. Whitespace alone
does not split `derives Eq Debug`: it is one TypeApply role reference.

## 4. Judge, priority, and owner boundary

`derives` is contextual only at owner-opened attachment points. The sink-free
`recognize_derives_attachment_start` yields to actual body/form starters,
separators, closes, ambient claims, and typed statement-owner newlines.

Struct may attach before its body or after a complete braced/tuple body. Type
may attach before its nominal/equality form or after an equality RHS. The shared
`drive_derives_clauses` handles roles, commas, `via`, repeated clauses, and
recovery once; owner adapters only select valid positions and resume their own
continuation.

## 5. Byte-exact CST worked examples

```text
struct Point derives Eq, Debug via key { value: Int }
```

(line 20607) orders `StructKw`, `Identifier`, then
`DerivesClause(DerivesKw, TypeExpression(Eq), Comma, TypeExpression(Debug),
ViaKw, Identifier(key))`, followed by the named body.

```text
struct Point { value: Int } derives Eq
```

(line 20614) places the trailing `DerivesClause` after the completed brace
body; its actual close is evidence for trailing attachment.

```text
type Id derives Eq = Int derives Debug
```

(line 20619) orders header `DerivesClause`, `Equals`, RHS `TypeExpression`,
then trailing `DerivesClause`. The addendum supplies qualitative child order,
not byte offsets, so this page does not invent ranges.

## 6. Parser-side AST shape

```rust
pub(crate) struct DerivesAttachment<'source> {
    position: DerivesAttachmentPosition,
    clause: DerivesClause<'source>,
}

pub(crate) struct DerivesClause<'source> {
    keyword: Range<usize>,
    roles: Vec<Recovered<Box<TypeExpression<'source>>>>,
    via: Option<DerivesVia<'source>>,
    range: Range<usize>,
}

pub(crate) struct DerivesVia<'source> {
    keyword: Range<usize>,
    target: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}
```

`StructDeclaration` and `TypeDeclaration` each own source-ordered
`Vec<DerivesAttachment<'source>>`; position remains AST identity, not a CST
wrapper.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| exact `derives` at boundary | one `Missing(DerivesRole::RoleReference)`; boundary non-consuming |
| malformed role then TypePrimary | inner `Error(Type::Primary)` and same-slot retry |
| malformed role reaches boundary | inner Type error only; no derives-missing cascade |
| leading/repeated comma | one missing role per committed empty item, then retry |
| comma before boundary / `via` / next `derives` | one missing role; contextual token stays available |
| exact `via` at boundary | one `Missing(DerivesRole::ViaTarget)` |
| malformed via target then identifier | one maximal via-target error and same-slot retry |
| attachment gap owned outside | no clause and no derives recovery |

One accepted keyword creates one clause node; one record creates one recovery
node. No missing separator is inferred between TypeExpression words.

## 8. Boundary and state-restoration contract

Role parsing uses the reusable `TypeExpressionScopedStopFrame`,
`TypeExpressionEpisodePolicy`, `type_expression_episode_depth`, and
`type_stop_is_active_in_current_episode`. Scoped `Derives`, `Via`, and Struct
header body-starter stops are visible only in the outer episode and suspend in
nested episodes. All probe, normal, recovery, and rollback exits restore state.

## 9. Yulang2 divergences

Yulang2 attached derives to a wider owner set. Current Yulang3 limits syntax to
Struct and Type, uses contextual rather than global reservation, typed recovery,
full ordinary TypeExpression roles, direct clause CST children, and no synthetic
attachment/separator nodes.

## 10. Known residual / deferred surface

No accepted derives-specific residual is recorded. Enum/Error/Act attachment,
role support, lowering, generated implementations, and semantic validation are
deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_derives_attachment_start`, `drive_derives_clauses`,
`parse_derives_attachments_isolated`, `parse_derives_clause_isolated`,
`parse_derives_via_isolated`, `commit_derives_attachments_isolated`,
`commit_derives_clause_isolated`, and `commit_derives_via_isolated`.

Fixtures include `derives_start_and_driver_follow_drv_j_and_restore_every_probe_state`,
`derives_role_episode_policy_fences_outer_stops_across_nested_type_episodes`,
`isolated_derives_direct_cst_adapter_is_byte_exact_lossless_and_ast_parity_checked`,
`derives_drv_r_recovery_rows_keep_ast_and_direct_slots_in_lockstep`,
`derives_gate_8_real_dispatch_is_atomic_across_every_owner_and_position`, and
`derives_gate_9_final_public_boundary_matrix_closes_scope_and_parity`.

