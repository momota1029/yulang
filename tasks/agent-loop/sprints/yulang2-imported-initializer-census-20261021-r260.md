# R260 — static census of Y2 imported root initializers

Status: primary-only source census; independent review pending. Read-only.
Parent R149 behavior and all general proof/production gates remain OPEN. No
compiler edits, tests, builds, sample executions or expected-output changes.

## Scope and method

Oracle commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`. Read only the exact
40 Y2 library source blobs frozen in R149 rev10. A primary script rechecked
every path with `git rev-parse <commit>:<path>` against the contract's exact
blob ID before scanning source lines. The scan was a locator/census aid, not a
replacement parser or an observed `LoadedFile` execution.

Reused owners and facts within their stated premises:

- R154 reviewed `module_map::register_block` distinguishes direct `Binding`
  children from `Expr` children and retains direct source order.
- R149/R152 pinned `typing::Evaluation` and the binding commit rule:
  `ComputedDef` is appended only for `FetchComputation` with runtime-root
  publication enabled.
- R259 pinned Value classification for references, application classification,
  lambda wrapping, tuple expansiveness and the local sample root subsequence.
- R152's copied act-body suppression evidence applies only to that actual
  copied-body route.

## Census result

Across the 40 exact blobs, the source-line locator found 307 direct-root
assignment-shaped `pub`/`our`/`my` headers. Their surface forms divide into
247 argument-shaped headers, 59 simple no-argument headers, and one
parenthesized single-head header `(mod)`. The simple headers' RHS forms are
only `builtin_op::...` references or integer literals (`2` and `512`). The
single-head `(mod)` header is also a typed builtin reference. No direct-root
expression statement was found in the imported files; unclassified column-zero
content was comments.

The parser/name helpers give the relevant semantic mapping: ApplyML/C headers
produce binding argument patterns (including the empty-call ApplyC pattern),
then the successful defined-lambda path returns `Computation::value`. Bare
typed names are not argument patterns. A simple identifier or the single-head
`(mod)` body is a name reference and lowers as a value; the two integer bodies
also lower as values. The source census therefore has no direct imported
binding whose constructor selects `Evaluation::Computation`.

A second bounded scan found 167 body-bearing member assignments nested under
root `role`, `impl`, and `type` declarations, with no argument-free member
candidate. These ordinary method bodies are lowered through receiver/argument
lambda paths; declarations without bodies are signatures. The separate act
body route is subject to the R152 copied-act publication suppression premise.
Local `my` assignments inside function bodies are not module root bindings.

Conditional result for the pinned standard-library closure: **no imported
ComputedDef initializer or direct Expr runtime root is indicated by the
reviewed root constructors and this 40-blob census**. Therefore the
sample-local roots from R259 are the only source candidates currently
identified:

```text
Types:   ComputedDef(answer), ComputedDef(name), Expr(pair.say)
Console: Expr(println ...), Expr(say: 1 + 2)
```

## Qualifications and falsifiers

The locator scanned source lines; it did not execute the Y2 parser or obtain
an exact per-module CST/DefId/root vector. Treat the zero-imported-initializer
result as a conditional source census, not an independently reviewed empty
set. It depends on the 40-file manifest covering the actual runtime source
closure, the scanner including every direct-root declaration form, the
argument-pattern mapping applying to all collected headers, successful
lowering/commit, and no other generated publication path. R149's import
closure and module composition remain separately required.

Falsifiers include a parsed direct-root expression omitted by the textual
locator, an argument-shaped binding not wrapped as a Value, a no-argument
binding body lowered as Computation, a role/impl/type member published as a
ComputedDef, or a generated/act path escaping the recorded publication rule.
The exact initialized module list, sample name-to-DefId join, accepted public
types, root specialization, Request reachability and output remain OPEN. No
parent proof or production gate closes here.

## Resource and review status

Primary-only source audit: 420 seconds charged in full, no carryover. No
independent reviewer or code writer participated. This locator/census is not
CLEAN and cannot independently activate implementation.
