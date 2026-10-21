# R260 — imported initializer census

Status: primary-only conditional source census; no independent review.

The exact 40-file Y2 standard-library closure was rechecked against the pinned
Git blob IDs. A root-source locator found 307 assignment-shaped declaration
headers: 247 with argument forms, 59 simple no-argument forms, and one
parenthesized single-head form. The simple bodies are builtin-operation
references or the two integer literals in `text/str.yu`; `(mod)` is another
builtin reference. The parser and lowering owners classify argument bindings
as lambda values and these simple reference/literal bodies as values. A
separate scan found no body-bearing role/impl/type member lacking an argument
form, and no imported direct-root expression statement.

Combined with the pinned root constructors, this gives a conditional result
that the imported 40-file closure contributes no ComputedDef or Expr runtime
root. If that holds at the exact parsed source interface, R259's sample-local
root subsequence is the runtime-root candidate list. The textual census is not
an observed parser/root vector and has no independent review. Full import
identity, composition, specialization, Request reachability, output, parent
proofs and production remain OPEN.

Exact scope and falsifiers: `tasks/agent-loop/sprints/yulang2-imported-initializer-census-20261021-r260.md`.
