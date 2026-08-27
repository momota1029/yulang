# standalone `impl` declaration shell

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative standalone impl-shell addendum（21011–21645行）、`IMD-G`、`IMD-J`、
`IMD-T`、`IMD-R` を要約する。

nine gate は `b39fd646`、`9a35a115`、`81f1cf43`、`5dfb48c6`、`83d5828a`、
`77b1d590`、`4f2978bb`、`cd66d695`、`481af012` で完了した。Gate 6/7 fixture が
見つけた adapter-local recovery fix は `b83c20b8`、`3ec7cd9a`、`b46b2a74`、
`46d82eec`、`4f2978bb` であり、shared TypeExpression episode machinery は変更しない。
このページは `d90b79b8` に対して照合した。

## 2. 対象と非対象

standalone impl は optional visibility、mandatory TypeExpression head、optional same-line
description、bodyless semicolon / braced / colon inline・indented canonical-statement body を持つ。
root Declaration と nested Statement は同じ owner を共有する。

Type-attached impl tail、declaration `with:` companion、Type colon/brace role-like body、Impl-specific
`via`、member/associated type、conformance semantics、HIR、resolver、inference、formatter は除外する。

## 3. BNF 相当の grammar

```text
ImplDeclaration := [ VisibilityKw Gimpl+ ] ImplKw Gimpl+ ImplHead [ ImplDescription ] Gimpl* ImplBody
ImplHead := RequiredTypeExpression(Impl::Head)
ImplDescription := Colon G0* RequiredTypeExpression(Impl::Description)
ImplBody := Semicolon | BracedStatementBlockExpression | ImplColonBody
ImplColonBody := Colon G0* Statement [ Semicolon ] | Colon IndentedStatementBlock
```

first colon は following trivia に physical newline がなければ description、あれば colon-body
introducer である。`:{` は episode policy が許す adjacent polymorphic-variant starter のままである。

## 4. Judge・priority・owner boundary

exact bare / visibility-led `impl` は Type 後、Binding 前で選ばれ、head/body success に依存しない。
head / description は outer `Colon`、`LeftBrace`、`Semicolon` stop を outer episode に fence した
full mandatory TypeExpression を使う。

body form は punctuation だけで開始する。head 終端 word を unstated inline body に split しない。
brace / indent body は existing statement-block owner を reuse し、colon-inline は canonical Statement を一度だけ呼ぶ。

## 5. byte-exact CST worked examples

```text
impl int: Eq;
```

（21315行）は `ImplDeclaration 0..13` である。`ImplKw 0..4`、head
`TypeExpression 5..8`、`Colon 8..9` を持つ `ImplDescription 8..12`、description
`TypeExpression 10..12`、`Semicolon 12..13` の順になる。

```text
impl point:
  our p.eq = true
```

（21338行）は `ImplDescription` を作らない。first colon 後の newline により
`IndentedStatementBlock` となり、opening trivia が newline / indent を所有する。

```text
impl Eq Int {
  our eq = id
}
```

（21349行）は `Eq Int` を一つの TypeApply head に保ち、existing
`BracedStatementBlockExpression` を `ImplDeclaration` 直下に置く。

## 6. parser 側 AST shape

```rust
pub(crate) struct ImplDeclaration<'source> {
    visibility: Visibility,
    head: Recovered<Box<TypeExpression<'source>>>,
    description: Option<ImplDescription<'source>>,
    body: Recovered<ImplBody<'source>>,
    range: Range<usize>,
}
```

committed scaffold は `ImplDescription`、`ImplBody`、`ImplColonBody` も表す。`ModBody` は
reuse しない。

## 7. typed recovery table

| condition | recovery と continuation |
| --- | --- |
| exact `impl` at boundary | `Missing(ImplRole::Head)` 一件。body-introducer は cascade しない |
| malformed head then TypePrimary | inner `Error(Type::Primary)` と same-slot retry |
| complete head at boundary | `Missing(ImplRole::BodyIntroducer)` 一件 |
| malformed introducer then starter | maximal body-introducer error 一件と same-slot retry |
| colon description at boundary | `Missing(ImplRole::Description)` 一件。body starter は retry 可 |
| malformed description reaches starter/boundary | inner Type error のみ。description/body-introducer は cascade しない |
| literal body colon at boundary | `Missing(ImplRole::Body, Statement)` 一件 |
| malformed inline body then Statement | body error 一件と same-slot retry |
| malformed indented first statement | existing `ImplRole::IndentedStatement` recovery のみ |
| brace close failure | existing `ClosingDelimiter` recovery のみ |

## 8. boundary と state-restoration contract

isolated / promoted adapter は input、line/sink、ambient/If、delimiter/stop、indentation、
TypeExpression episode depth、type owner、ML、positional-fence state を normal / recovery / rollback
で restore する。Gate 7 は isolated adapter の sink leak と body-starter-probe rollback を修正した。

## 9. Yulang2 divergences

Yulang3 は standalone visibility/head/description/body spelling を保つが、typed no-cascade recovery、
full TypeExpression episode fencing、canonical statement body を使う。Y2 silent close / generic invalid
token / heuristic punctuation-free inline split / rejected Impl-specific `via` branch は移植しない。

## 10. known residual / deferred surface

accepted impl-specific residual はない。deferred surface は Type-attached `impl`、declaration `with:`
companion attachment、Type colon/brace role-like body form、Impl-specific `via`、member semantics、
downstream HIR/resolver/inference/formatter である。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_impl_statement_intro`, `parse_impl_declaration_isolated`,
`parse_impl_after_head_ast`, `parse_impl_body_ast`,
`parse_impl_colon_body_ast`, `commit_impl_declaration_isolated`,
`commit_impl_after_head_isolated`, `commit_impl_body_isolated`,
`commit_impl_colon_body_isolated`。

fixture:
`impl_statement_intro_is_exact_isolated_and_rolls_back_every_probe_state`,
`impl_type_expression_episode_policy_is_phase_exact_nested_and_state_balanced`,
`isolated_impl_declaration_ast_selects_description_and_all_body_forms`,
`isolated_impl_declaration_direct_cst_is_lossless_and_matches_ast_shapes`,
`isolated_impl_body_recovery_retries_one_malformed_run_without_cascade`,
`impl_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners`,
`impl_gate_9_final_public_boundary_matrix_closes_scope_and_parity`。

