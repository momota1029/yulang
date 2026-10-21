# R251 result — ordered Tuple source carrier

Status: implementation result; unreviewed. R149 and parent proof gates remain
open.

## Decision

The source meaning needed by the R149 arbitrary-finite positional product path
is now explicit: `()` is Unit; `(x)` is Group; `(x,)` is a singleton Tuple;
and multiple direct parenthesized expression children are an ordered Tuple,
including parser-accepted implicit-newline-separated items. A trailing comma
adds no child. Recovered syntax and `ExpressionDelimitedSeparator` remain
unsupported. This is a primary source-mapping decision, not a claim of proved
language-wide semantics.

## Implementation

`LocalSourceForm::Tuple { elements }` retains one authentic child index for
each real direct child. The builder allocates slots in source order and pushes
work in reverse so its LIFO traversal still publishes source-order occurrence
identities. The dynamic tuple-index vector capacity is included in
`retained_arena_bytes`. Unit and Group retain their prior forms.

The ordinary source carrier can now represent tuples, including a parenthesized
colon-application element. This remains a rich source record. It does not add a
canonical `ResolvedExpr::Tuple`, inference term, candidate graph node, runtime
value, closed scheme, or imported semantic binding.

## Evidence

- `cargo test -p yu-hir --lib` passed all 139 unit tests.
- Focused HIR tuple carrier test passed for arities one through three, a final
  comma, and implicit-newline-separated items. It checks element values, source
  ranges, source occurrence order, and dynamic index retention.
- Unit, Group, malformed tuple, and recovery boundary tests passed.
- The adjacent colon application carrier test passed after being updated to
  inspect the newly retained two-element tuple.
- `cargo test -p yu-hir` reached the integration suites but failed two assertions
  in `simple_module_resolution`: one expects `my w = f 1` to lower as an Error,
  and another expects `my g y = h 1` to retain an Error body. Those paths do not
  contain parenthesized syntax and were not changed by this patch; the failures
  are unresolved and are not counted as passing evidence.
- The ordinary expression source-carrier integration suite passed after its
  rollback fixture was changed from a now-supported tuple to an unsupported
  recovery form.
- `rustfmt --check` reports drift in both edited Rust files, and the same check
  also fails on both `HEAD` versions. The newly added sections were aligned to
  rustfmt output without reformatting the files' unrelated existing code.
- No independent review or source/native proof was performed.

## Remaining obligations

Canonical ordinary HIR admission, inference generation and equal-arity
comparison, extrusion/capture/freshening, candidate and closed scheme export,
left-to-right tuple evaluation, imports, effects, host writes, output, and the
original Console and Types playground samples remain open. The two full HIR
suite failures also need baseline adjudication.
