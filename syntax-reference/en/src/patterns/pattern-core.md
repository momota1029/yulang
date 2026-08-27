# Pattern core and parenthesized patterns

## 1. Status, authority, and last verification

The original Authoritative first-slice Pattern addendum is lines 6629–7242 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its opening status is stale, but the closing signature records review, confirmation, and user approval. Current parenthesized separators are revised by the Authoritative layout addendum at 9314–9696; ambient-boundary recovery is revised by the Authoritative `ASOB-G` addendum at 18358–19161.

Core implementation began in `4ec436cc`; current parenthesized behavior also depends on `81ef211d`, `f38c77d8`, `d3778e13`, and `0da2d26e`. The later `9323ce68` attachment addendum adds `PatternTypeAnnotation` to the shared AST; its grammar has a separate reference page. This page was checked against `f9393004`.

## 2. Scope and non-scope

The core is an independent, fixed-precedence Pattern Pratt family: ordinary and sigil identifiers, decimal integers, contiguous symbol patterns, parenthesized patterns, `as` aliases, and `|` alternation. It does not use expression `OperatorChain`, dynamic binding powers, or `BpVec`.

This page covers the parenthesized container's current comma-or-layout-newline behavior. List and record primaries, trailing Pattern type annotations, calls, paths, ML application, literals, resolution, lowering, exhaustiveness, and binding validation remain separate grammar or semantic work.

## 3. BNF-equivalent grammar

```text
Pattern := Pattern@Lowest
Pattern@P := PatternPrimary { PatternTail(P) } [ PatternTypeAnnotation ]
PatternTail(P) := G* PatternAliasTail if P <= Alias | G* PatternAlternationTail if P <= Alternation
PatternAliasTail := AsKw G+ Identifier
PatternAlternationTail := Pipe G* Pattern@Alternation
PatternPrimary := IdentifierPattern | IntegerPattern | SymbolPattern | ParenthesizedPattern | ListPattern | RecordPattern
SymbolPattern := Colon!Identifier
ParenthesizedPattern := LParen OpeningTrivia [ Pattern@Lowest { ParenthesizedPatternSeparator Pattern@Lowest } [ ParenthesizedPatternSeparator ] ] RParen
ParenthesizedPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(parenthesized_pattern_base)
```

The first-slice order is `Alternation < Alias`; alternation therefore makes `A | (B | C)`. The later annotation suffix is included only to reflect the current shared `Pattern` AST. An implicit newline is a separator only when its following indentation is at most the base captured immediately after `(`; a deeper newline remains with the current Pattern continuation.

## 4. Judge, priority, and owner boundary

At an operand position the NUD judge prefers contiguous `:identifier` before an active caller `Colon` stop. If that composite is absent and colon is an active stop, it remains caller-owned. Sigil names precede ordinary words; `as` is contextual only in tail position, and `|` is a fixed Pattern token rather than a dynamic expression operator.

After accepting `(`, the parenthesized owner captures its layout base, pushes its delimiter/local comma-and-close scope, and owns explicit commas plus qualifying newline boundaries. It emits no synthetic separator for an implicit newline. Own matching `)` wins first; propagated caller right closes return non-consumingly. `ASOB-G` additionally lets a strict ambient dedent or active If companion veto a local implicit-boundary decision. The close-recovery driver converges AST cursor ownership onto the pre-existing direct-CST result.

## 5. Byte-exact CST worked examples

The original and revising addenda contain exact CST trees, but no byte-range-annotated CST tree for these examples; this page intentionally does not invent ranges.

```text
A | B as c
```

Design lines 6901–6918 show an outer `Pattern` with `IdentifierPattern A`, then `PatternAlternationTail` containing `Pipe` and a recursive RHS `Pattern`. The RHS owns `IdentifierPattern B` and `PatternAliasTail` with `AsKw` and identifier `c`; the left primary is never reparented under the tail.

```text
(:foo, _bar,)
```

Design lines 6920–6937 show one outer `Pattern` whose `ParenthesizedPattern` owns raw parentheses and commas, a two-token `SymbolPattern` (`Colon`, `Identifier foo`), and an `IdentifierPattern` with `SigilIdentifier _bar`.

```text
(A
B)
```

Design lines 9549–9551 revise this to a valid two-element `ParenthesizedPattern` at base zero. The physical newline remains literal trivia between child `Pattern` nodes; it creates neither `Missing(Comma)` nor a synthetic separator node.

## 6. Parser-side AST shape

The actual `Pattern` in `crates/yu-syntax/src/grammar/pattern.rs` has recovered `head`, ordered `tails`, optional `type_annotation`, and `range`. `PatternPrimary` currently includes identifier, integer, symbol, `Parenthesized`, `List`, and `Record` variants. The core parenthesized variant stores `open`, recovered element Patterns, literal `trailing_comma`, recovered `close`, and `range`.

`PatternTail` is `Alias(PatternAliasTail)` or `Alternation(PatternAlternationTail)`. The alias keeps its keyword and a recovered ordinary binding; alternation keeps its pipe and recovered boxed RHS. The Pattern core does not classify identifiers as bindings, constructors, or wildcards.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| absent primary | one `PatternRole::Primary` Missing, with caller boundary unconsumed |
| malformed primary then NUD | one maximal primary Error and same-slot retry |
| `:` without an adjacent name | malformed symbol plus `PatternRole::SymbolName` Missing unless colon is caller-owned |
| `A as` | keep `AsKw`; one `PatternRole::AliasBinding` Missing at the terminal boundary |
| `A |` | keep `Pipe`; one recovered RHS Pattern primary |
| leading comma in parens | one `PatternRole::ParenthesizedElement` Missing, then next-element retry |
| adjacent same-line element | one `PatternRole::ParenthesizedSeparator` Missing and same-position retry |
| malformed/missing parenthesized close | one closing-delimiter Error or Missing; own/caller-close ownership stays distinct |
| qualifying newline | valid implicit boundary, no missing comma or synthetic separator |
| ASOB-vetoed boundary | local container stops and returns the ambient gap; it does not consume the outer owner |

The direct path records one recovery node and record per range. Nested recovery keeps its Pattern or closing-delimiter role and never creates an additional outer diagnosis for the same cause.

## 8. Boundary and state-restoration contract

Every parenthesized entry and exit balances delimiter, stop, and layout frames. The layout base is captured once after the opener. AST/direct fixtures cover normal items, implicit boundaries, malformed recovery, caller-close handoff, ambient If veto, and exact rollback of scanner/sink state. `ASOB-G` requires ambient/If, delimiter/stop, indentation, expression/type-owner, ML, and positional-fence state to restore across nested exits.

## 9. Yulang2 divergences

Yulang3 preserves the independent fixed Pattern Pratt family, contiguous symbol spelling, alias/alternation ordering, and layout-separated parenthesized forms. Unlike Yulang2, an implicit newline is represented by literal trivia and adjacent children, not a source-absent `Separator` node. Typed Missing/Error recovery replaces generic invalid tokens and silent close behavior.

## 10. Known residual / deferred surface

`ASOB-G` explicitly leaves non-companion same-indent competition and some caller boundaries hidden behind a missing nested delimiter as known residual families. The Cast addendum later characterizes its own stricter four-condition instance; neither rule grants a general "outer owner always wins" exception.

Deferred grammar includes Pattern annotation details, list/record forms, constructor tails, literals, and ML application. Deferred semantic work includes wildcard meaning, binding sets, alias scope, type constraints, exhaustiveness, Pattern HIR, and lowering.

## 11. Implementation and regression cross-reference

Key functions in `crates/yu-syntax/src/grammar/pattern.rs` are `parse_pattern`, `parse_pattern_with_outer_missing_role`, `parse_direct_pattern`, `parse_pattern_bp`, `parse_pattern_primary`, `parse_parenthesized_pattern`, `parse_pattern_delimited_items_ast`, `commit_direct_parenthesized_pattern`, `commit_direct_pattern_delimited_items`, `drive_parenthesized_pattern_close_recovery`, and `outer_pattern_close_stop_pending`.

Fixtures include `identifiers_and_integer_primaries_have_the_fixed_pattern_vocabulary`, `symbol_pattern_is_two_adjacent_tokens_and_never_an_expression_tail`, `parenthesized_patterns_accept_comma_or_layout_newline_boundaries`, `parenthesized_close_recovery_converges_ast_onto_existing_direct_ownership`, `ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`, `dynamic_operator_tables_cannot_change_pattern_cst`, `excluded_forms_remain_unconsumed_after_a_first_slice_pattern`, and `pattern_caller_close_propagation_is_right_close_only`.
