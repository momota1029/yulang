# `forall` types

## 1. Status, authority, and last verification

The Authoritative forall addendum is lines 13431–13980 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its current ambient-boundary behavior is refined by `ASOB-G` at 18358–19161 and malformed-newline behavior by `TMN` and positional-fence authority at 16557–17289.

Implementation commits are `b79df9d2`, `f7bacb34`, `57afb683`, and `f8b95909`. This page was checked against `063da888`.

## 2. Scope and non-scope

Forall adds `for 'a 'b: T` as a contextual TypePrimary only at canonical type NUD positions. It owns ordered apostrophe-only binders, mandatory colon, full recursive body, bounded layout, and phase-specific recovery.

Statement `for`, LED/ML `for`, non-apostrophe binders, use-site wiring, type semantics, HIR/lowering, diagnostics text, and formatting are out of scope.

## 3. BNF-equivalent grammar

```text
ForallType := ForKw ForallTypeBinder { ForallTypeBinder } ForallColonTrivia Colon ForallBodyTrivia TypeExpression
ForallTypeBinder := ForallBinderBoundary ApostropheTypeBinderName
ForallBinderBoundary := NonEmptyTriviaWithoutPhysicalNewline | NonEmptyTriviaWithDeeperFollowingIndent(forall_base)
ApostropheTypeBinderName := Apostrophe UnicodeIdentifierBody
```

The `forall_base` snapshot is taken immediately after accepted `for`. Binder boundaries are non-empty; colon/body gaps may be empty. Equal-or-shallower newline never becomes forall-owned trivia.

## 4. Judge, priority, and owner boundary

At canonical NUD position, exact maximal `for` wins before an identifier and cuts to forall. `forx`, `forall`, and `for_` remain identifiers. At a TypeApply LED position, exact `for` is an ordinary identifier seed, not a re-scanned forall.

The three phases are FirstBinder, BinderOrColon, and Body. Before any binder, only apostrophe binders or literal colon establish progress; after a binder, apostrophe begins another binder while a non-binder primary is a missing-colon body retry. Raw forall is terminal: its body owns path/call/apply/arrow; only grouping can put an outer tail after it.

## 5. Byte-exact CST worked examples

The addendum provides complete CST trees but no byte-range-annotated trees; no ranges are invented here.

```text
for 'a: A -> A
```

Design lines 13641–13662 show `ForallType` owning `ForKw`, one `ForallTypeBinder`, colon-side trivia, and a nested TypeExpression whose arrow belongs to the body.

```text
for
  'a
  'b:
    Pair('a, 'b)
```

Design lines 13664–13697 show each binder owning its own leading newline/indentation boundary, while the deeper colon-to-body trivia belongs to `ForallType`.

```text
(for 'a: 'a)::Result
```

Design lines 13897–13902 show grouping as the required route for a `TypePathTail` after forall.

## 6. Parser-side AST shape

`TypePrimary::Forall(ForallType)` stores `keyword`, ordered recovered `binders`, recovered `colon`, recovered boxed `body`, and `range`. `ForallTypeBinder` stores its recovered leading `boundary`, apostrophe name, and range.

There is no delimiter close or separator slot. A missing whole binder remains an incomplete list item; a missing boundary belongs to an otherwise complete binder. This mirrors CST ownership and recovery cardinality.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `for` at EOF/boundary | one `TypeRole::ForallBinder` Missing; no colon/body cascade |
| adjacent binder | one `TypeRole::ForallBinderBoundary` Missing, then same-position binder retry |
| malformed first binder | one ForallBinder Error; retry binder or colon skeleton |
| accepted binder at EOF/boundary | one `TypeRole::ForallColon` Missing; no body cascade |
| non-binder after accepted binder | one missing ForallColon, then same-position full body retry |
| malformed continuation before binder/colon/body | one exclusive Binder or Colon Error selected by earliest retry target |
| accepted colon with missing/malformed body | one `TypeRole::ForallBody` Missing/Error; boundary remains owned |

Comma and semicolon are not binder separators. All scans stop before active stops, closes, caller boundaries, qualifying newline, and retry candidates; one cause yields one committed record.

## 8. Boundary and state-restoration contract

Forall pushes no delimiter or layout frame. Its bounded trivia probes and body call compose existing stop, delimiter, type-ML, owner, episode, and positional-fence state, restoring every state on normal, recovery, and rollback exits. AST/direct share recognition, phase, cut, and safe-point predicates.

## 9. Yulang2 divergences

Yulang2 parser code supports contextual NUD `for`, binder repetition, full body recursion, and terminality, but has no dedicated forall fixture. Yulang3 intentionally narrows binders to apostrophe-only, records typed phase recovery and bounded gaps, and replaces generic `InvalidToken` behavior with no-cascade Missing/Error records.

## 10. Known residual / deferred surface

The general hidden-boundary residual is documented by `ASOB-G`; this page adds no forall-specific exemption. Use-site integration, universal-type semantics, HIR/lowering, inference, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_forall_type`, `commit_direct_forall_type`, `scan_forall_keyword`, `scan_forall_binder`, `scan_forall_invalid_run`, `forall_recovery_candidate`, `forall_recovery_boundary_pending`, `parse_forall_body_for_ast`, and `commit_direct_forall_body`.

Fixtures include `forall_type_primary_owns_a_non_delimited_binder_sequence_and_body`, `forall_is_nud_only_apostrophe_only_and_terminal`, `forall_recovery_keeps_its_phase_slots_non_cascading`, and `forall_bounded_phases_defer_a_live_if_companion_before_consuming_trivia`.
