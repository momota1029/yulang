# Standalone `impl` declaration shell

## 1. Status, authority, and last verification

This page summarizes the Authoritative standalone impl-shell addendum, lines
21011–21645 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`:
`IMD-G`, `IMD-J`, `IMD-T`, and `IMD-R`.

The nine gates landed in `b39fd646`, `9a35a115`, `81f1cf43`, `5dfb48c6`,
`83d5828a`, `77b1d590`, `4f2978bb`, `cd66d695`, and `481af012`. Adapter-local
recovery fixes discovered by Gate 6/7 fixtures are `b83c20b8`, `3ec7cd9a`,
`b46b2a74`, `46d82eec`, and `4f2978bb`; they do not alter the shared
TypeExpression episode machinery. This page was checked against `d90b79b8`.

## 2. Scope and non-scope

A standalone impl has optional visibility, mandatory TypeExpression head,
optional same-line description, and bodyless semicolon, braced, or colon
inline/indented canonical-statement body. It is shared by root Declaration and
nested Statement.

Type-attached impl tails, declaration `with:` companions, Type colon/brace
role-like bodies, Impl-specific `via`, members/associated types, conformance
semantics, HIR, resolver, inference, and formatter are excluded.

## 3. BNF-equivalent grammar

```text
ImplDeclaration := [ VisibilityKw Gimpl+ ] ImplKw Gimpl+ ImplHead [ ImplDescription ] Gimpl* ImplBody
ImplHead := RequiredTypeExpression(Impl::Head)
ImplDescription := Colon G0* RequiredTypeExpression(Impl::Description)
ImplBody := Semicolon | BracedStatementBlockExpression | ImplColonBody
ImplColonBody := Colon G0* Statement [ Semicolon ] | Colon IndentedStatementBlock
```

The first colon is description only when its following trivia has no physical
newline; otherwise it is the colon-body introducer. `:{` remains an adjacent
polymorphic-variant starter where the episode policy permits it.

## 4. Judge, priority, and owner boundary

Exact bare/visibility-led `impl` is selected after Type and before Binding,
without depending on head/body success. Head and description use full mandatory
TypeExpression with outer `Colon`, `LeftBrace`, and `Semicolon` stops fenced to
the outer episode.

Body forms start only with punctuation. The parser never splits a head-ending
word into an unstated inline body. Braced and indented bodies reuse existing
statement-block owners; colon-inline calls canonical Statement once.

## 5. Byte-exact CST worked examples

```text
impl int: Eq;
```

(line 21315) has `ImplDeclaration 0..13`: `ImplKw 0..4`, head
`TypeExpression 5..8`, `ImplDescription 8..12` with `Colon 8..9` and
description `TypeExpression 10..12`, then `Semicolon 12..13`.

```text
impl point:
  our p.eq = true
```

(line 21338) has no `ImplDescription`: the newline after the first colon makes
an `IndentedStatementBlock`, whose opening trivia owns the newline and indent.

```text
impl Eq Int {
  our eq = id
}
```

(line 21349) keeps `Eq Int` as one TypeApply head and puts the existing
`BracedStatementBlockExpression` directly under `ImplDeclaration`.

## 6. Parser-side AST shape

```rust
pub(crate) struct ImplDeclaration<'source> {
    visibility: Visibility,
    head: Recovered<Box<TypeExpression<'source>>>,
    description: Option<ImplDescription<'source>>,
    body: Recovered<ImplBody<'source>>,
    range: Range<usize>,
}
```

The committed scaffold also represents description/body variants with
`ImplDescription`, `ImplBody`, and `ImplColonBody`; no `ModBody` is reused.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| exact `impl` at boundary | one `Missing(ImplRole::Head)`; no body-introducer cascade |
| malformed head then TypePrimary | inner `Error(Type::Primary)` and same-slot retry |
| complete head at boundary | one `Missing(ImplRole::BodyIntroducer)` |
| malformed introducer then starter | one maximal body-introducer error and same-slot retry |
| colon description at boundary | one `Missing(ImplRole::Description)`; body starter may retry |
| malformed description reaches starter/boundary | inner Type error only; no description/body-introducer cascade |
| literal body colon at boundary | one `Missing(ImplRole::Body, Statement)` |
| malformed inline body then Statement | one body error and same-slot retry |
| malformed indented first statement | existing `ImplRole::IndentedStatement` recovery only |
| brace close failure | existing `ClosingDelimiter` recovery only |

## 8. Boundary and state-restoration contract

Isolated and promoted adapters prove restoration of input, line/sink, ambient/If,
delimiter/stop, indentation, TypeExpression episode depth, type owner, ML, and
positional-fence state across normal, recovery, and rollback. Gate 7 fixed a
sink leak and body-starter-probe rollback in the isolated adapter.

## 9. Yulang2 divergences

Yulang3 preserves standalone visibility/head/description/body spelling while
using typed no-cascade recovery, full TypeExpression episode fencing, and
canonical statement bodies. It does not import Y2 silent close, generic invalid
tokens, heuristic punctuation-free inline splitting, or Y2's rejected
Impl-specific `via` branch.

## 10. Known residual / deferred surface

No accepted impl-specific residual is recorded. Deferred surfaces are exactly
Type-attached `impl`, declaration `with:` companion attachment, Type colon/brace
role-like body forms, Impl-specific `via`, member semantics, and downstream
HIR/resolver/inference/formatter work.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_impl_statement_intro`, `parse_impl_declaration_isolated`,
`parse_impl_after_head_ast`, `parse_impl_body_ast`,
`parse_impl_colon_body_ast`, `commit_impl_declaration_isolated`,
`commit_impl_after_head_isolated`, `commit_impl_body_isolated`, and
`commit_impl_colon_body_isolated`.

Fixtures include `impl_statement_intro_is_exact_isolated_and_rolls_back_every_probe_state`,
`impl_type_expression_episode_policy_is_phase_exact_nested_and_state_balanced`,
`isolated_impl_declaration_ast_selects_description_and_all_body_forms`,
`isolated_impl_declaration_direct_cst_is_lossless_and_matches_ast_shapes`,
`isolated_impl_body_recovery_retries_one_malformed_run_without_cascade`,
`impl_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners`, and
`impl_gate_9_final_public_boundary_matrix_closes_scope_and_parity`.

