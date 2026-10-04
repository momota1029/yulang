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
One finite source-generated immediate-application witness is now closed for an
empty lexical environment and no State/reference operations. It confirms
receipt-before-force and the actual Pure Value-entry path, but does not define
callback-slot domain admission; that execution witness itself does not cover
captures, aliases, imports, divergence, future use, or resumptions.
For supplied finite source graphs, a query-independent proof relation also
preserves immutable lexical aliases, captures, and recursive labels without
requiring the callable hole to inhabit its checked denotation. This is
structural transport conditional on supplied derivations; arbitrary imports
and source-State replacement/read remain outside it. See the same progress
record for the exact relation and limit.
One conditional structural subgate is closed for typed filling into a finite
supplied open derivation graph: the skeleton, slot/profile positions,
distinct receipts, typed paths, and joint `K,D` incidence transport when
matching typing premises are supplied. This does not construct semantic
admission or close context/execution closure; the whole-carrier and
bound-inclusion clauses remain open.
Do not add a carrier/API, independent effect-port subtyping, or a global
transitive relation between concrete successes without a demonstrated need
and the required authority.

## Broader milestone blockers

- Milestone 3 (finite symbolic presentation) still lacks source-wide
  comparison/context closure, complete source realization, and effective
  joint residual/projection for open Records and feedback. A reviewed bounded
  theorem now gives a regular witness for unguarded structural constraints
  whose flexible classes occur only as inequality roots and whose other
  endpoints are closed descriptors. It does not cover shifted open-descriptor
  equations, principal residuals, or source acceptance; see
  [root-only regular-witness theorem](../notes/progress/2026-10-04-root-only-regular-witness.md).
  There is no class-3 impossibility result. One bounded source-origin subgate is closed:
  normative callback B supplies one occurrence-indexed initial
  `F_lit <: F_cb` root per eligible callback-literal derivation, with its
  context/profile references retained under admissible transport. This does
  not establish finite derived-query contexts or any global closure theorem;
  see [callback initial-root enumeration](../notes/progress/2026-10-04-callback-initial-root-enumeration.md).
- The source local-State operational bridge is incomplete. Static
  `StateSlotId` and pure continuation restart are decided, but the source
  equations for dynamic ownership, read/update replacement, captured access,
  and repeated resumption are not established. Do not infer runtime identity
  from `StateSlotId` or introduce primitive heap mutation. See the
  source-state boundary in
  [concrete-compatibility-boundary.md](../notes/design/2026-10-03-concrete-compatibility-boundary.md).
  One same-invocation observation is already fixed by the stable-core fixture:
  a `get` closure created before `r.update` later returns `"start!"`, not its
  initial `"start"` capture. The general transition, distinct activations,
  escape, and multi-shot resumption remain open. A separate two-slot fixture
  expects independent updates `(11, 21)`, without covering repeated activation
  identity. Frozen Oracle inspection adds only a characterization of
  `ref.update` continuation flow; its `var_ref` State-backed implementation
  is separate from the custom-ref local-buffer fixture. The successor
  State/restart derivation remains open. See
  [local-State capture observation](../notes/progress/2026-10-04-local-state-capture-observation.md).
  The bounded derivation audit located the missing bridge: callback response
  delivery/raw resumption reaches the local assignment, but no successor
  clause connects pure restart to a later read through the pre-existing
  capture. This remains a proof obligation, not a selected runtime rule; the
  fixture fixes only the `"start!"` observation.
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
- [Root-only regular-witness theorem](../notes/progress/2026-10-04-root-only-regular-witness.md)
- [Ordinary computation semantics](../notes/design/2026-10-02-ordinary-computation-semantics-package.md)
- [Value-entry bind/projection progress](../notes/progress/2026-10-04-value-entry-bind-projection.md)
- [Callback policy and task-ledger compactification](../notes/progress/2026-10-04-callback-policy-and-task-compaction.md)
- [Bounded local-State capture observation](../notes/progress/2026-10-04-local-state-capture-observation.md)
- [Pre-compaction chronological task ledger](../notes/progress/2026-10-04-task-ledger-before-compaction.md)

The archived ledger preserves prior investigation, counterexamples, reviewer
findings, and intermediate handoffs verbatim apart from its archive notice.
Later entries and this compact summary determine current status; archival
movement does not downgrade or supersede any user decision or design status.
