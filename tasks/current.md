# Current task: replace Yulang type inference with SCC-intrusion inference

Updated: 2026-10-04. Branch: research/simple-sub-intrusion.

## Objective and authority

Prove the SCC-intrusion successor sound, principal, and compatible with
Oracle's final well-typed-program capability on the supported envelope, then
implement the fully reviewed and approved inference machine. This objective
remains active; compiler implementation is not authorized yet.

Authority order is current user decisions, in-scope Authoritative designs,
active rules, confirmed code/test invariants, then general practice. The design
index is navigation only; source designs govern. See
[design authority](../rules/design-authority.md) and
[design index](../notes/design/INDEX.md).

## Closed decisions

- **Inequality:** one endpoint-dependent `A <: B` solver. Variable-bound
  propagation may use transitivity; successful concrete comparisons may not
  be composed. Casts/adapters are evidence or realizations from concrete
  inequality resolution. Optional-record compatibility is not transitive
  structural subtyping.
- **Function/effects:** source introduction/context selects Pure or Handler
  before Function-port interpretation. Effects are coupled ports, not
  independently-subtyped Types. Covariant rows are canonical flat forms;
  contravariant concrete-bearing descriptors retain only structure needed for
  witnessed partial reverse addition using existing subtraction evidence.
  `never`, `Any`, empty rows, and polarized solver bounds remain distinct.
- **Callback literal:** B is the normative/reference constraint generation:
  expected context selects Handler/boundary before body generation, endpoints
  are independently synthesized, and the completed interface is checked by
  one ordinary `F_lit <: F_cb`. A is permitted only as B-equivalent constraint
  scheduling/partial evaluation; it must preserve acceptance, principal
  solutions, method/adapter choices, and residual/evidence semantics. Stronger
  endpoint assignment/equality is invalid.
- **Existing Pure callback value:** preserve its actual role and §21 entry; a
  callback slot supplies a typed invocation view without rewriting the value.

The governing semantic sources are [concrete compatibility](../notes/design/2026-10-03-concrete-compatibility-boundary.md)
and [callback context delivery](../notes/design/2026-10-03-callback-context-delivery.md).
Oracle behavior around `Never`, `Any`, effects, and references is
characterization only where it conflicts with these decisions.

## Active proof gates

**Next gate — Pure-value callback/Function theorem.** Establish whole-carrier
admission/domain inclusion, endpoint/profile and linked-contribution adequacy,
and observation-bound inclusion across legal histories. Reuse existing
`Rel_C`, `K,D`, paths, receipts, occurrence/incidence, `Flow`/`Observe`, and
subtraction evidence. Do not add a carrier/API or independent port-subtyping
rule without identifying a concrete unrepresentable fact and obtaining
authority. Detailed clauses and conditional results:
[value-entry bind/projection](../notes/progress/2026-10-04-value-entry-bind-projection.md).
The direct main-theorem attack confirms one owning gate: source-to-endpoint
adequacy for the original role-indexed Function query. It must construct
checked-challenge admission independently of query success and establish both
`D_checked ⊆ D_actual` and full observation-bound inclusion. Even granting
equal domains and execution correspondence for a stateless terminating Pure
identity, execution coverage does not prove that every observation admitted
by the actual endpoint bound factors through the existing argument/body/result
composition and linked view. The exact missing bound premise and its minimal
logical countermodel are in
[direct main-gate attacks](../notes/progress/2026-10-04-direct-main-gate-attacks.md).
The source reference `Sem` is already the exact collecting relation; endpoint
presentations `P_i` may conservatively cover it. The missing proof concerns
factorization of that presentation's full bound, not choosing a new meaning
for `Sem`. This is not a Yulang program counterexample, State exclusion does
not close the bound gap, and no carrier or semantic choice follows.

**Other open gates:**

- **Structural solving / Milestone 3:** the finite constrained residual
  presentation remains distinct from regular-witness decidability and
  principal/effective projection. The exact existence boundary is regular
  completion when descriptor equations prefix-shift addresses while active
  comparisons descend suffixes with variance and Record-width conditions.
  This remains open; it is not an undecidability result. The direct MSO route
  is invalid, and standard ranked exact-shape subtyping does not directly
  encode mandatory Record width. Bounded results and failed scoped encodings
  are not general impossibility:
  [open residual design](../notes/design/2026-10-03-open-residual-factorization.md),
  [root-only result](../notes/progress/2026-10-04-root-only-regular-witness.md),
  [queue probes](../notes/progress/2026-10-04-fixed-descriptor-queue-encoding.md),
  and [direct main-gate attacks](../notes/progress/2026-10-04-direct-main-gate-attacks.md).
- **Source State/reference bridge:** derive dynamic ownership, read/update
  replacement, captured access, and repeated resumption; the `start!` fixture
  fixes only one observation:
  [State bridge record](../notes/progress/2026-10-04-local-state-capture-observation.md).
- **Global source bridge/lifecycle:** first-class-reference/import realization,
  complete `EnvStore`/`JointWF`, source-wide acceptance/principality, and
  generalization/SCC lifecycle remain open.

No bounded result closes these gates or authorizes compiler implementation.

## Governing designs and preserved history

- [SCC-intrusion redesign charter](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
- [Scoped constraint solving](../notes/design/2026-10-03-scoped-constraint-solving.md)
- [Finite bound/replay closure](../notes/design/2026-10-03-finite-bound-replay-closure.md)
- [Source context finite closure](../notes/design/2026-10-03-source-context-finite-closure.md)
- [Ordinary computation semantics](../notes/design/2026-10-02-ordinary-computation-semantics-package.md)

Prior investigations, counterexamples, reviews, and handoffs remain in
[`notes/progress/`](../notes/progress/) and the
[pre-compaction chronological ledger](../notes/progress/2026-10-04-task-ledger-before-compaction.md).
This summary changes no design status, authority, or historical user decision.
