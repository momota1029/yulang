# Current task: replace Yulang type inference with SCC-intrusion inference

Updated: 2026-10-04. Branch: `research/simple-sub-intrusion`.

## Objective and authority

Prove the SCC-intrusion successor sound, principal, and compatible with
Oracle's final well-typed-program capability on the supported envelope; then
implement the fully reviewed and approved inference machine. This full goal
remains active. Compiler implementation is not yet authorized.

Authority order is the user's current decisions, in-scope `Authoritative`
designs, repository rules, confirmed code/test invariants, then general
practice. The index is navigation only; source designs remain authoritative.
See [design-authority.md](../rules/design-authority.md) and
[INDEX.md](../notes/design/INDEX.md).

## Closed decisions

- **One inequality solver:** every query is `A <: B`, with endpoint-dependent
  resolution. Variable-bound propagation may use transitivity; successful
  concrete comparisons cannot be composed into another concrete comparison.
  Casts/adapters are evidence or realizations from concrete-query resolution.
  Source: [concrete-compatibility-boundary.md](../notes/design/2026-10-03-concrete-compatibility-boundary.md).
- **Function/effect model:** function effects are coupled interface ports,
  not independently-subtyped `Type`s. Covariant rows are canonical flat;
  contravariant concrete-bearing descriptors preserve only structure needed
  for witnessed partial reverse addition using existing subtraction evidence.
  `never`, `Any`, empty rows, and polarized internal bounds remain distinct.
  Source: same compatibility design, §§3–8, and
  [callback-context-delivery.md](../notes/design/2026-10-03-callback-context-delivery.md).
- **Source roles and execution:** function introduction/expected context
  selects Pure or Handler before port interpretation. Callback-position
  unannotated literals receive the expected boundary before body constraints
  and use Handler; an existing Pure value preserves its actual role and §21
  entry while the callback slot supplies its invocation view. Whole arguments
  are reified inertly; Value entry forces in the same invocation.
- **Callback endpoint policy:** B is the normative/reference constraint
  generation semantics: select Handler/boundary before body constraints,
  independently synthesize parameter/body/result endpoints, then check the
  completed literal interface once by ordinary `F_lit <: F_cb`. A is permitted
  only as scheduling/partial-evaluation optimization of B's logical
  consequences, with observational and solution equivalence; it cannot change
  acceptance, principal solutions, method/adapter choices, or residual/evidence
  semantics, nor impose stronger endpoint equality/assignment. This user
  clarification is recorded in the callback design §2.1.
- **Historical distinctions:** Oracle observations characterize its
  implementation but do not define successor semantics where they conflict
  with the user's decisions.

## Active proof gate

The callback/Function theorem remains open for the already-constructed Pure
value passed through a known callback slot. Reuse `Rel_C`, `K,D`, paths,
receipts, occurrence/incidence, `Flow`/`Observe`, and subtraction evidence.
The selected port locations are settled:

```text
d⁻ -> received whole argument / designated Force view
d⁺ -> that argument-origin contribution at complete slot CallView
b⁺ -> body/result-consumer contribution at J_call
```

The current bounded identity-context result has a non-circular candidate
skeleton and conditional exact-execution correspondence, but does not prove
the complete interface clauses. The remaining obligations are:

1. Define query-independent admission for whole-carrier contexts and
   well-formed environments/stores, then prove plugging/execution closure and
   `D_checked ⊆ D_actual`.
2. Prove endpoint/profile adequacy and linked contribution over all legal
   challenges in one fiber.
3. Establish observation-bound inclusion `P_actual ⊆ P_checked`; exact
   execution equality alone is insufficient when `P` is an upper bound.
4. Preserve aliases, state, invocation delimiters, and every legal response,
   future-use, and resumption history without changing the tested Pure role
   or §21 entry.

Review evidence and exact conditional claims are in
[value-entry-bind-projection.md](../notes/progress/2026-10-04-value-entry-bind-projection.md).
Do not add a carrier/API, independent effect-port subtyping, or a global
transitive relation between concrete successes without a demonstrated need
and the required authority.

## Broader milestone blockers

- Milestone 3 (finite symbolic presentation) still lacks source-wide
  comparison/context closure, complete source realization, and effective
  joint residual/projection for open Records and feedback. There is no
  class-3 impossibility result.
- The source local-State operational bridge is incomplete. Static
  `StateSlotId` and pure continuation restart are decided, but the source
  equations for dynamic ownership, read/update replacement, captured access,
  and repeated resumption are not established. Do not infer runtime identity
  from `StateSlotId` or introduce primitive heap mutation. See the
  source-state boundary in
  [concrete-compatibility-boundary.md](../notes/design/2026-10-03-concrete-compatibility-boundary.md).
  The key discriminator is what a closure captured before an update reads
  afterward; derive this from the intended State expansion before treating it
  as a new user decision.
- General first-class-reference/import realization, complete `EnvStore` /
  `JointWF`, source-wide acceptance/principality, and generalization/SCC
  lifecycle remain open. No implementation authorization follows from the
  bounded callback or structural results.

## Governing sources and history

- [SCC-intrusion redesign charter](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
- [Callback context delivery](../notes/design/2026-10-03-callback-context-delivery.md)
- [Concrete compatibility boundary](../notes/design/2026-10-03-concrete-compatibility-boundary.md)
- [Scoped constraint solving](../notes/design/2026-10-03-scoped-constraint-solving.md)
- [Open residual factorization](../notes/design/2026-10-03-open-residual-factorization.md)
- [Ordinary computation semantics](../notes/design/2026-10-02-ordinary-computation-semantics-package.md)
- [Value-entry bind/projection progress](../notes/progress/2026-10-04-value-entry-bind-projection.md)
- [Callback policy and task-ledger compactification](../notes/progress/2026-10-04-callback-policy-and-task-compaction.md)
- [Pre-compaction chronological task ledger](../notes/progress/2026-10-04-task-ledger-before-compaction.md)

The archived ledger preserves prior investigation, counterexamples, reviewer
findings, and intermediate handoffs verbatim apart from its archive notice.
Later entries and this compact summary determine current status; archival
movement does not downgrade or supersede any user decision or design status.
