# Concrete compatibility boundary audit

Date: 2026-10-03
Branch: `research/simple-sub-intrusion`
Mode: M3 semantic/source-authority clarification
Review budget: one architect pre-write audit, one implementation-source explorer,
and two independent bounded reviewers (`compiler_referee`, `spec_auditor`)

## Decision recorded

The user's current decision allows transitivity for bound propagation among
type variables. A concrete type pair is checked by a local compatibility
judgment that can resolve cast/adaptation evidence. Compatibility successes
do not enter one transitive concrete subtype closure. The supplied optional
Record chain is accepted by Oracle although its direct string-to-int optional
Record comparison is rejected. These observations constrain the successor
design but do not yet specify field adaptation or optional-Record source
syntax.

`notes/design/2026-10-03-concrete-compatibility-boundary.md` records the
relation split, preserves the declared mathematical scope of the reviewed
structural theorems, and makes evidence-preserving compatibility normalization
the next research gate. It grants no implementation authority.

## Bounded repository evidence

- `yu-solver::TermView` and `InferenceSession::constrain_live` represent
  polarized Function comparisons and variable-bound replay, but no Record or
  adapter constructor.
- `yu-types` has no Record or adapter constructor in its closed type algebra.
- Successor HIR excludes cast declarations from the current resolved
  expression envelope. The parser and stable-core corpus contain cast syntax
  and an implicit value-cast example.
- Successor named-Record type syntax requires `name: Type`; optional Record
  pattern defaults are different syntax and semantics.
- The typed-boundary adapter theorem covers fixed-shape Function/Thunk
  realization. It does not decide concrete compatibility or optional Records.

The new draft passed bounded independent semantic and conformance reviews with
no findings. The compiler referee did not audit the whole call graph, frozen
cast implementation, or full predecessor proofs; the spec auditor did not run
Oracle or tests. No code or test expectations changed. `git diff --check`
passed. No tests, builds or measurements were run. Measurement budget
consumed: 0.

## Next gate

Define concrete compatibility outcomes with retained conversion evidence for
the optional-Record discriminator, then prove guarded query generation from
variable-bound propagation and evidence-preserving residual factorization.
Keep source-wide context finiteness, unknown Record shapes, effectful
interfaces, lifecycle and implementation open until their own gates close.
