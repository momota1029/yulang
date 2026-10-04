# Current task: replace Yulang type inference with SCC-intrusion inference

Updated: 2026-10-04. Branch: research/simple-sub-intrusion.

## Objective and authority

Prove the SCC-intrusion successor sound, principal, and compatible with Oracle's
final well-typed-program capability on the supported envelope; then implement
the fully reviewed and approved inference machine. This full objective remains
active. Compiler implementation is not authorized yet.

Authority order is current user decisions, in-scope Authoritative designs,
active rules, confirmed code/test invariants, then general practice. The design
index is navigation only; source designs govern. See
[design authority](../rules/design-authority.md) and
[design index](../notes/design/INDEX.md).

## Closed decisions

- **One inequality solver:** every query is A <: B, resolved by endpoint
  shape. Variable bounds may propagate transitively; successful concrete
  comparisons may not be composed. Casts/adapters are evidence or realizations
  from concrete-query resolution. Optional-record compatibility is not an
  ordinary transitive structural subtype. See
  [concrete compatibility](../notes/design/2026-10-03-concrete-compatibility-boundary.md).
- **Function/effect representation:** effects are coupled Function interface
  ports, not independently-subtyped Types. Covariant rows use canonical flat
  form; contravariant concrete-bearing descriptors preserve only structure
  needed for witnessed partial reverse addition using existing subtraction
  evidence. never, Any, empty rows, and polarized internal bounds remain
  distinct. Source introduction/context selects Pure or Handler before port
  interpretation. See the same design and
  [callback contract](../notes/design/2026-10-03-callback-context-delivery.md).
- **Callback literal policy — closed:** B is the normative/reference
  constraint-generation semantics. Expected callback context arrives before
  body generation and selects Handler/boundary; endpoints are independently
  synthesized; the completed interface is checked by one ordinary
  F_lit <: F_cb. A is allowed only as scheduling/partial evaluation of B's
  logical consequences, with observational and solution equivalence. It cannot
  impose stronger endpoint equality or change acceptance, principal solutions,
  method/adapter choices, or residual/evidence semantics. The durable
  clarification is in callback design §2.1.
- **Existing Pure callback value — closed source rule:** preserve its actual
  Pure role and §21 entry; the callback slot supplies a typed invocation view
  without rewriting the underlying value. Whole arguments are constructed
  inertly and Value entry forces within the same invocation.
- Oracle behavior around Never, Any, effects, and references is
  characterization only where it conflicts with these decisions.

## Current proof gates and blockers

**Immediate gate: Pure-value callback/Function theorem.** Prove whole-carrier
admission and D_checked ⊆ D_actual; endpoint/profile and linked-contribution
adequacy; and P_actual ⊆ P_checked, preserving aliases, state, invocation
delimiters, responses, future use, and resumptions. Reuse Rel_C, K,D, paths,
receipts, occurrence/incidence, Flow/Observe, and subtraction evidence.
The selected contribution locations are settled: d⁻ maps to the received
whole argument/designated Force view; d⁺ maps that argument-origin contribution
to the complete slot CallView; b⁺ maps body/result-consumer contribution to
J_call. Their proof status and conditional transport are detailed in the
linked progress record.
Do not add a carrier/API or independent port-subtyping rule without a concrete
unrepresentable fact and authority. Exact bounded status and conditional
lemmas are in [value-entry bind/projection progress](../notes/progress/2026-10-04-value-entry-bind-projection.md).

**Other open gates:**

- **Structural solving / Milestone 3:** source-wide comparison/context
  closure, complete source realization, and effective joint residual/projection
  for open Records and feedback. The root-only regular-witness result is
  bounded; shifted open-descriptor equations, full fibers/principality, and
  source acceptance remain open. No general impossibility result exists; three
  queue-encoding patterns fail in scoped probes only. See
  [queue encoding probes](../notes/progress/2026-10-04-fixed-descriptor-queue-encoding.md),
  [open residual factorization](../notes/design/2026-10-03-open-residual-factorization.md)
  and [root-only theorem](../notes/progress/2026-10-04-root-only-regular-witness.md).
- **Source local State/reference bridge:** dynamic ownership, read/update
  replacement, captured access, and repeated resumption are not derived. The
  start! fixture fixes one observation only; do not infer runtime identity
  from StateSlotId or add primitive heap mutation. See
  [local-State observation](../notes/progress/2026-10-04-local-state-capture-observation.md)
  and the source-State boundary in concrete compatibility.
- **Global source bridge/lifecycle:** first-class-reference/import
  realization, complete EnvStore/JointWF, source-wide
  acceptance/principality, and generalization/SCC lifecycle remain open.

No bounded callback or structural result authorizes compiler implementation.

## Governing sources and preserved history

- [SCC-intrusion redesign charter](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
- [Callback context delivery](../notes/design/2026-10-03-callback-context-delivery.md)
- [Concrete compatibility boundary](../notes/design/2026-10-03-concrete-compatibility-boundary.md)
- [Scoped constraint solving](../notes/design/2026-10-03-scoped-constraint-solving.md)
- [Open residual factorization](../notes/design/2026-10-03-open-residual-factorization.md)
- [Finite bound/replay closure](../notes/design/2026-10-03-finite-bound-replay-closure.md)
- [Source context finite closure](../notes/design/2026-10-03-source-context-finite-closure.md)
- [Ordinary computation semantics](../notes/design/2026-10-02-ordinary-computation-semantics-package.md)
- [Callback B root enumeration](../notes/progress/2026-10-04-callback-initial-root-enumeration.md)
- [Callback policy and prior compaction](../notes/progress/2026-10-04-callback-policy-and-task-compaction.md)
- [Pre-compaction chronological ledger](../notes/progress/2026-10-04-task-ledger-before-compaction.md)

Detailed investigations, counterexamples, reviewer findings, and intermediate
handoffs remain in linked progress records and the archived ledger. This
summary changes no design status, authority, or historical user decision.
