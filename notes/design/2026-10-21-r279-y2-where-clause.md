# R279 — Yulang2 declaration-local `where` syntax

Status: checkpointed parser-only addendum under Authoritative R149's unchanged-source scope.
No method selection or typeclass semantics are introduced here.

## Source evidence

The pinned `std::core::fmt` source places `where` constraints as the first
indented lines under function bodies and `impl` bodies. It uses both one and
multiple independent prerequisites (`'a: Display`, `'ok: Display`,
`'err: Display`); other pinned modules include an applied role head such as
`'container: std::data::fold::Fold 'item`. The Y3 parser currently treats these
lines as ordinary statements and emits root `ErrorGroup`s, so the exact source
cannot publish its syntax artifact.

R149 requires authentic role candidates and prerequisite discharge from the
unchanged source. Parsing the clause is a necessary source boundary, but the
resulting CST alone cannot establish that a candidate matches or that its
prerequisites hold.

## Syntax ownership

Recognize a consecutive `where` prefix only at the beginning of an indented
function-binding or implementation body. Each complete clause is a dedicated
`WhereClause` CST node with the real keyword and ordered type-expression
children around the colon. The block then resumes its ordinary statement/body
grammar. The parser must leave the first non-where item pending for that normal
grammar and keep malformed clauses bounded to their source line.

The prefix is declaration-owned. Ordinary nested indented statement blocks do
not acquire `where` syntax from this addendum. No source rewriting, role lookup,
constraint generation, solver change, HIR admission or runtime behavior is
authorized by this syntax node.

## Verification boundary

The R278 exact fmt census contains 36 diagnostics, partitioned as 21 root
`ErrorGroup`s, 7 `OperatorChain` `ErrorGroup`s, 7 missing `CaseArm`s, and one
`Missing` `StringEscape`. The last row is retained explicitly; the previous
three-category subtotal did not account for it. R279 asserts the complete
partition. Valid `where` prefixes remove root recovery at declaration
boundaries and allow nested body parsing to continue; the parser then reports
previously hidden `CaseArm` and `OperatorChain` failures. The total therefore
falls less than the root count.

R149 inference, authentic implementation selection, mixed module execution,
exact Types/Console outputs, source/native proof and production remain OPEN.
