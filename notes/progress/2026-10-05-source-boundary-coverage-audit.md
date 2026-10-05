# Current source-boundary coverage for concrete inequality adequacy

Date: 2026-10-05
Status: source-coverage characterization; no source-typing or implementation authority
Branch/HEAD inspected: `research/simple-sub-intrusion` / `c267ae509`
Governing decision: one endpoint-dependent inequality solver; successful concrete checks are not transitively composable. See [concrete compatibility boundary](../design/2026-10-03-concrete-compatibility-boundary.md) §1.
Related obstruction: [concrete transitivity proof-interface obstruction](2026-10-05-source-adequacy-concrete-transitivity-obstruction.md)

## Discriminating source form

The expression `x as Int` provides a useful coverage probe because it has a
surface syntax node for an explicit type boundary. It does not currently reach
the production constraint solver as a concrete compatibility query.

- `crates/yu-syntax/src/expression/tails/type_annotation.rs`,
  `type_annotation_tail_normalized`, constructs `TypeAnnotationTail` and
  parses a required full `TypeExpression` after `as`.
- `crates/yu-hir/src/lib.rs`, `ChainParser::expression` and
  `structural_continuation`, preserve the annotation as an outer HIR value
  whose first child is the preceding expression and whose remaining children
  retain the annotation target.
- `direct_atom` admits only one integer-literal or identifier-expression
  child. `crates/yu-hir/src/module.rs`, `lower_simple_chain`, maps other
  associated chains to `SimpleChainLowering::Unsupported`; the binding-body
  and direct-root owners publish `ResolvedExpr::Error` with
  `UnsupportedExpression`.
- `ResolvedExpr` has only Lambda, Integer, Name and Error forms.
  `crates/yu-solver/src/lib.rs`, `ConstraintBatch::collect`, consumes this
  semantic HIR and has no annotation/cast/check conversion case that emits a
  local inequality or stores its realization evidence.
- `crates/yu-core/src/lib.rs` currently has only its module doc comment; no
  typed adapter realization is present there.

Existing tests confirm association keeps the annotation outside the reduced
dynamic segment (`type_annotation_receives_the_reduced_dynamic_segment` and
`associates_structural_postfixes_before_the_enclosing_chain`). Existing HIR
tests also confirm non-leaf applications and unsupported binding bodies yield
error values rather than typed applications or conversions. These tests are
implementation coverage evidence only; they do not define which source forms
the successor must accept.

## Consequence for the proof gate

The chain

    x : {foo?: string}
    check at {}
    check at {foo?: int}

still refutes treating successful concrete endpoint checks as one transitive
relation. Current semantic HIR does not implement a source path that realizes
those two checks, so this witness does not show a production bug or evidence
erasure in an accepted current program. Conversely, current rejection is not
authority to make such source forms permanently unsupported.

The missing source-to-solver contract remains: which source forms establish
individual inequality boundaries, which endpoint each boundary exports, and
how any selected cast/adapter evidence is realized across consecutive
boundaries. Callback application is a separate unresolved translation; this
audit does not equate an application with one completed Function inequality.

No compiler files or tests were changed or run. No source-acceptance choice,
new solver carrier, or production inference change is selected.
