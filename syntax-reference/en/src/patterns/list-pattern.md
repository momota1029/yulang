# List patterns

## 1. Status, authority, and last verification

The original Authoritative ListPattern addendum is lines 8019–8612 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its comma-only separator scope is explicitly superseded by the Authoritative layout addendum at 9314–9696; ambient recovery is further revised by `ASOB-G` at 18358–19161. The original opening status is stale, while each relevant addendum's closing signature records review, confirmation, and user approval.

Implementation commits are `af9c85f4`, `c852d878`, `81ef211d`, `f38c77d8`, and `0da2d26e`. This page was checked against `f9393004`.

## 2. Scope and non-scope

A ListPattern is a bracketed sequence of ordinary Pattern items or literal spread items. Empty lists, trailing commas, arbitrary spread count and position, full recursive Pattern spread RHS, typed recovery, and caller-boundary handoff are in scope.

Record patterns, Pattern annotations, constructor/ML tails, expression list literals, spread matching semantics, cardinality validation, resolution, typing, Pattern HIR, lowering, and diagnostics wording are out of scope.

## 3. BNF-equivalent grammar

```text
ListPattern := LBracket OpeningTrivia [ ListPatternItem { ListPatternSeparator ListPatternItem } [ ListPatternSeparator ] ] RBracket
ListPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(list_pattern_base)
ListPatternItem := Pattern@Lowest | ListPatternSpreadItem
ListPatternSpreadItem := DotDot G* Pattern@Lowest
```

The base is captured immediately after `[` from opening trivia and incoming indentation. A newline with following indentation `<= list_pattern_base` is a separator; a deeper newline is continuation. Semicolon is never a List separator. `..tail` and `.. tail` are spread forms, whereas `...` and `..+` are not prefix-split into `DotDot`.

## 4. Judge, priority, and owner boundary

After accepting `[`, the ListPattern owns a bracket delimiter and local comma/right-bracket stops. The item judge first recognizes the matching close, then exact `DotDot`, then an ordinary Pattern NUD, then a comma missing-item boundary, then malformed recovery. List-local commas never become Catch handler or arm separators.

Explicit comma wins over a qualifying newline in the same boundary cluster. Implicit newline is literal trivia, not a synthetic token. Own `]` wins first; propagated caller right closes return non-consumingly. `ASOB-G` vetoes a local implicit boundary for strict ambient dedent or an active If companion, while ordinary same-indent non-companion competition remains outside that mechanism.

## 5. Byte-exact CST worked examples

The ListPattern and layout addenda contain exact CST shapes but no byte-range-annotated CST trees for these examples; no ranges are invented here.

```text
[head, ..middle, tail]
```

Design lines 8289–8311 show `Pattern > ListPattern` with direct ordinary `Pattern` children for `head` and `tail`, raw `Comma` tokens, and one `ListPatternSpreadItem` containing `DotDot` plus the RHS Pattern `middle`.

```text
[..left, ..right,]
```

Design lines 8313–8336 show two `ListPatternSpreadItem` children and a raw trailing comma. Spread multiplicity does not select a different outer node.

```text
[
  head
  ..middle
  tail
]
```

Design line 9574 classifies this as base two, three ListPattern items, and a valid trailing implicit boundary. The newlines and indentation remain literal trivia; no `Separator` node is added.

```text
[a
b]
```

Design line 9575 classifies an equal-indent newline at base zero as two valid items. Design line 9576 contrasts a deeper newline as continuation of the first Pattern rather than a second List item.

## 6. Parser-side AST shape

`PatternPrimary::List(ListPattern)` is the current AST primary. `ListPattern` stores `open`, recovered ordered `items`, literal `trailing_comma`, recovered `close`, and `range`. Each `ListPatternItem` is either a direct `Pattern` or a `Spread(ListPatternSpreadItem)`; the spread node stores its `marker`, recovered boxed RHS Pattern, and range.

An accepted `DotDot` is retained even when its RHS is incomplete. The AST keeps item order and literal trailing-comma evidence but does not duplicate every separator token or decide any spread semantics.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `[]` / `[a,]` | valid empty or trailing-comma list; no recovery |
| `[,a]` / `[a,,b]` | one `PatternRole::ListItem` Missing per absent item, then same-position item retry |
| same-line next item or spread | one `PatternRole::ListSeparator` Missing and same-position retry |
| `[a; b]` | non-empty `PatternRole::ListSeparator` Error; `b` retries as the next item |
| malformed ordinary item | one `PatternRole::ListItem` Error and same-slot retry |
| `[..]` / `[..,a]` | preserve `ListPatternSpreadItem`; one `PatternRole::ListSpreadRhs` Missing; comma/close remains owned |
| `[..@tail]` | one RHS Error and same-slot retry at `tail` |
| `[...,a]` / `[..+,a]` | malformed item Error; do not create a spread node by prefix split |
| missing/mismatched `]` | one ListPattern closing-delimiter Missing/Error; caller boundary remains non-consuming |
| ambient-vetoed newline | stop at the outer gap with exactly the local recovery required so far |

Each committed range maps to one recovery node and one record. Nested list frames balance exactly once on normal close, terminal boundary, and recovery.

## 8. Boundary and state-restoration contract

The bracket frame captures its base once after the opener and restores delimiter, stop, layout, scanner, and sink state on every exit. AST/direct fixtures cover nested brackets, outer arm arrows, handler commas, implicit newlines, malformed items, missing closes, propagated caller closes, and ambient If veto. `ASOB-G` also requires exact restoration of ambient/If, indentation, expression/type-owner, ML, and positional-fence state.

## 9. Yulang2 divergences

Yulang3 preserves bracket ownership, ordinary versus spread items, unrestricted spread placement, and layout-separated item forms. It represents implicit newline with literal trivia rather than Yulang2's empty `Separator` node, and uses typed Missing/Error plus same-position retry rather than generic invalid tokens or silent close behavior.

## 10. Known residual / deferred surface

`ASOB-G` documents residual cases where a caller boundary hidden behind a missing nested delimiter is neither strict dedent nor an active If companion. These are not silently treated as success. The later Cast addendum gives a separate condition-based characterization for Cast-contained ListPattern cases.

Deferred work includes record-list unification, spread matching and capture semantics, multiplicity/position validation, list element typing, Pattern HIR, lowering, and expression list literals.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/pattern.rs`: `parse_list_pattern`, `commit_direct_list_pattern`, `parse_pattern_delimited_items_ast`, `commit_direct_pattern_delimited_items`, `commit_direct_pattern_delimited_item`, `recover_pattern_delimited_separator_or_close`, and `outer_pattern_close_stop_pending`.

Fixtures include `list_patterns_accept_comma_or_layout_newline_and_keep_spread_items`, `list_pattern_recovery_preserves_item_and_separator_boundaries`, `list_pattern_typed_recovery_contract_has_direct_coverage_for_every_list_row`, `ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`, `binding_list_pattern_preserves_else_arm_after_an_ambient_veto`, `pattern_delimited_malformed_recovery_returns_the_same_ambient_gap`, and `pattern_caller_close_propagation_is_right_close_only`.
