# shared `derives` clause attachment

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative shared derives addendum（20278–21010行）、`DRV-G`、`DRV-J`、`DRV-T`、
`DRV-R` を要約する。

nine gate は `919766cf`、`8ace7256`、`47a63de3`、`695523ca`、`b6c9a391`、
`9a6ab93e`、`2cd4a1e7`、`e00f9a6b`、`69589b5d`、`a3174886` で表される。
Gate 1 は neutral 1a / consumer 1b に split される。`919766cf` は後続 impl / cast
addendum が使う reusable neutral TypeExpression episode infrastructure を記録する。
このページは `d90b79b8` に対して照合した。

## 2. 対象と非対象

shared `DerivesClause` は Struct header/trailing と Type header/trailing-equality に attach
する。exact `derives`、一つ以上の TypeExpression role reference、literal comma、optional
`via Identifier` を所有する。

declaration / statement intro、delimiter owner、implicit separator、role resolver、derive plan、
generated impl、field lookup、semantic diagnostic は作らない。

## 3. BNF 相当の grammar

```text
DerivesClause :=
    DerivesKw DerivesRoleTrivia RequiredTypeExpression(Derives::RoleReference)
    { DerivesRoleGap Comma DerivesRoleTrivia RequiredTypeExpression(Derives::RoleReference) }
    [ DerivesRoleGap ViaKw DerivesViaTrivia RequiredRawIdentifier(Derives::ViaTarget) ]
DerivesKw := exact contextual word "derives"
ViaKw := exact contextual word "via" inside an accepted DerivesClause
```

attachment は qualifying same-line / strictly-deeper trivia を使う。whitespace だけでは
`derives Eq Debug` を split せず、一つの TypeApply role reference とする。

## 4. Judge・priority・owner boundary

`derives` は owner-opened attachment point だけで contextual になる。sink-free
`recognize_derives_attachment_start` は actual body/form starter、separator、close、ambient claim、
typed statement-owner newline に yield する。

Struct は body 前または complete braced/tuple body 後、Type は nominal/equality form 前または
equality RHS 後に attach できる。shared `drive_derives_clauses` が role / comma / `via` /
repeated clause / recovery を一度だけ扱い、owner adapter は valid position と continuation だけを選ぶ。

## 5. byte-exact CST worked examples

```text
struct Point derives Eq, Debug via key { value: Int }
```

（20607行）は `StructKw`、`Identifier`、続く
`DerivesClause(DerivesKw, TypeExpression(Eq), Comma, TypeExpression(Debug),
ViaKw, Identifier(key))`、named body の順である。

```text
struct Point { value: Int } derives Eq
```

（20614行）は complete brace body の後に trailing `DerivesClause` を置く。actual close が
trailing attachment の evidence である。

```text
type Id derives Eq = Int derives Debug
```

（20619行）は header `DerivesClause`、`Equals`、RHS `TypeExpression`、trailing
`DerivesClause` の順である。追補は qualitative child order を示すだけで byte offset を
与えないため、ここでも range を発明しない。

## 6. parser 側 AST shape

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

`StructDeclaration` と `TypeDeclaration` は source order の
`Vec<DerivesAttachment<'source>>` を持つ。position は CST wrapper でなく AST identity である。

## 7. typed recovery table

| condition | recovery と continuation |
| --- | --- |
| exact `derives` at boundary | `Missing(DerivesRole::RoleReference)` 一件。boundary non-consuming |
| malformed role then TypePrimary | inner `Error(Type::Primary)` と same-slot retry |
| malformed role reaches boundary | inner Type error のみ。derives Missing は cascade しない |
| leading/repeated comma | committed empty item ごとに missing role 一件と retry |
| comma before boundary / `via` / next `derives` | missing role 一件。contextual token は使用可能 |
| exact `via` at boundary | `Missing(DerivesRole::ViaTarget)` 一件 |
| malformed via target then identifier | maximal via-target error 一件と same-slot retry |
| attachment gap owned outside | clause / derives recovery とも作らない |

accepted keyword 一つは clause node 一つ、record 一つは recovery node 一つになる。
TypeExpression word 間の missing separator は推測しない。

## 8. boundary と state-restoration contract

role parse は `TypeExpressionScopedStopFrame`、`TypeExpressionEpisodePolicy`、
`type_expression_episode_depth`、`type_stop_is_active_in_current_episode` を使う。
scoped `Derives`、`Via`、Struct header body-starter stop は outer episode だけで visible になり、
nested episode では suspend する。probe / normal / recovery / rollback exit はすべて state を restore する。

## 9. Yulang2 divergences

Yulang2 はより広い owner set へ derives を attach した。current Yulang3 は Struct / Type に限定し、
global reservation でなく contextual authority、typed recovery、full ordinary TypeExpression role、
direct clause CST child、synthetic attachment/separator 不使用を選ぶ。

## 10. known residual / deferred surface

accepted derives-specific residual はない。Enum/Error/Act attachment、role support、lowering、
generated implementation、semantic validation は deferred である。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_derives_attachment_start`, `drive_derives_clauses`,
`parse_derives_attachments_isolated`, `parse_derives_clause_isolated`,
`parse_derives_via_isolated`, `commit_derives_attachments_isolated`,
`commit_derives_clause_isolated`, `commit_derives_via_isolated`。

fixture:
`derives_start_and_driver_follow_drv_j_and_restore_every_probe_state`,
`derives_role_episode_policy_fences_outer_stops_across_nested_type_episodes`,
`isolated_derives_direct_cst_adapter_is_byte_exact_lossless_and_ast_parity_checked`,
`derives_drv_r_recovery_rows_keep_ast_and_direct_slots_in_lockstep`,
`derives_gate_8_real_dispatch_is_atomic_across_every_owner_and_position`,
`derives_gate_9_final_public_boundary_matrix_closes_scope_and_parity`。

