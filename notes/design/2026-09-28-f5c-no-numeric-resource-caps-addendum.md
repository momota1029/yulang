# F5c no-numeric-resource-cap addendum

Status: Authoritative
Approved-by: user
Approved-at: 2026-09-28
Reviewed-by: spec_auditor, compiler_referee, performance_auditor (round-one and targeted delta reviews closed with no unresolved findings)
Scope: F5c numeric admission, runtime resource failure, and complexity evidence for production acceptance
Related authority: F5 §§9, 14, 26, 34, 36; reviewed flat indexed candidate §§2–8, 13, 15, 17, 20, 22
Decision: remove deterministic numeric input-size and charged-work caps for F5c; do not impose a fixed runtime cutoff. Keep checked representation and allocation failure handling, and assess ordinary inputs by phase-specific asymptotic complexity and resource evidence.
Supersedes: F5c clauses requiring numeric draft-size/repeat-work thresholds or a numeric supported-input boundary before production acceptance, and the bounded-envelope preference in rules/design-authority.md within F5c only; see §5 for exact scope.

## 1. User direction and scope

On 2026-09-28, the user selected removal of F5c input-size and computation-work
policy caps. The user also rejected a fixed computation-time cutoff and asked
for ordinary asymptotic behavior. Full polynomial behavior for every possible
input is not required if ordinary inputs are adequately handled.

This addendum applies only to F5c. It does not authorize numeric caps or a
resource-policy change in F5e Function products, §44 per-use routing, other
compiler phases, or public runtime APIs.

The objective is a lightweight successful path for ordinary source shapes and
the explicit F5 scale families already named by the F5 authority. Before
production acceptance, the owning phases must state their complexity in terms
of actual source, graph, occurrence, comparison, and output dimensions; avoid
unnecessary rescans and copies on those families; and reconcile their actual
physical capacities. These are complexity and observation obligations, not
input quotas. This direction does not assert a global polynomial bound in
compact source size.

## 2. Resource failure contract

F5c does not reject otherwise representable input because a configured byte,
node, edge, draft, or charged-work threshold was reached. It attempts the work
using checked representation arithmetic and the existing allocation owners.

- The solver checks its own count, ID, and span arithmetic before constructing
  an indexed input; an unrepresentable value follows the existing solver
  `IdentityExhausted` path. A malformed direct `yu-types` indexed input remains
  `InvalidDraft`; a valid direct input that exhausts checked index, capacity,
  or byte accounting remains `IdentityExhausted`. These finite representation
  ranges are safety constraints, not selected product thresholds.
- A catchable fallible-reserve failure follows the error path owned by that
  solver component or finalizer attempt. A solver-produced `InvalidDraft` is
  an internal invariant failure and is not remapped to a new availability
  variant. Every returned F5c solve error publishes no partial scheme, fact,
  receipt, provenance, route marker, or `SolvedModule`.
- Each valid indexed-finalizer attempt retains the existing transaction and
  failure-epoch rules: rollback its logical overlay once, reconcile retained
  capacity, allow retry after a representable reserve failure, and terminally
  poison only on the specified checked aggregate overflow. A returned
  validation, callback, or commit failure after a valid attempt begins advances
  the epoch once; a solver failure before entering `yu-types` does not advance
  that epoch. Terminal poison does not advance it again. Unwind restores logical
  state, reconciles representable capacity, advances the epoch once, and resumes
  the original panic. Earlier completed transactions remain governed by their
  existing owner/API contract.
- The process may abort or be terminated by the allocator/operating system on
  actual memory exhaustion, and an unusually expensive finite input may run
  for a long time. In those cases no returned diagnostic, retry, or completion
  is promised.
- Resource exhaustion is a runtime availability failure. It does not make
  valid source language-level undefined behavior, and it never relaxes Rust
  memory safety, checked indexing, or transaction invariants.
- Every successful solve preserves the existing Oracle-observable scheme,
  ordering, facts, diagnostics, and counter values.

Exact physical lane, retained-byte, and peak accounting remains required as
observation and review evidence. It is not compared with a compiler policy
threshold. Checked projected dimensions still precede growth where required
to protect `usize`/`u32` representation; this includes the Authoritative live
intermediate-graph node-plus-child-slot census. Removing policy ceilings does
not remove those checked censuses or pre-growth representation checks.

The existing solve-wide work meter remains an exact checked observation of its
specified pre-finalization operations; it has no configured work ceiling and
must not be reset at component/root boundaries. A representational overflow
in the meter still returns `IdentityExhausted`. Byte-sum overflow in a
production accounting owner follows that owner's existing exhaustion and
publication rules; overflow in a test-only independent ledger fails the
witness and is not a separate product admission policy. The meter's scope does
not extend to F5e or §44.

## 3. Complexity contract

Complexity claims must name their dimensions and owning phase. Do not describe
F5 §36's normalization bound as an end-to-end F5c bound.

- The authoritative closed-normalization contract remains
  `O(N + W + C_norm)`: `N` finalized DAG nodes, `W` descriptor words,
  and `C_norm` the exact prescribed descriptor-word comparisons. The
  canonical preordering remains `O(N + W)`. Existing public counters retain
  their actual-operation meanings and exact schedules.
- Producer, replay, materialization, and R filtering must report work against
  their actual summary states, incidences, root-local contexts, candidate
  masks, visited/copied trace hops, and path-expanded occurrences. Reuse is
  permitted only where root, polarity, mask, binder, reentry order, and
  rollback state remain equivalent.
- Indexed finalization must retain its bounded-pass work over supplied nodes,
  incidences, bounds, and explicitly owned scratch. Its current F5a callback
  contract and F5c dense producer invariants remain unchanged.
- A shared summary may expand into many occurrences. A diagnostic run of the
  current materializer on a synthetic binary shared-summary DAG had 13
  memoized nodes and 24 stored child edges, but produced 8,191 unshared output
  nodes and 8,190 edges at depth 12; this measured the existing boxed output,
  not a flat candidate's physical peak. The flat candidate's §17
  occurrence-preserving materializer has the same shape of work but no
  comparable resource sample in the completed capture. This growth is linear
  in expanded occurrences and exponential in compact depth. It is a candidate
  implementation choice, not a proven semantic lower bound.
- The ordinary-family gate is limited to the exact source recipes in the
  completed source-Lambda plan and the parameterized F5 §26/§34 builders. It
  is evidence for those families, not a whitelist of accepted source or a
  global polynomial-in-source promise. The phase owners must provide
  source-level upper-bound formulas before production acceptance; finite
  measurements may corroborate those formulas and capacity constants but
  cannot establish asymptotic order by themselves.

| Ordinary family | Dimensions | Required source-level work bound |
| --- | --- | --- |
| Identity, constant, resolved module-name, and productive self-recursive Lambda recipes | fixed-size recipe | `O(1)` per solve, apart from source parsing |
| Productive Function SCC ring | `N` definitions and `N` internal uses in `my n{i} x = n{(i+1)%N}`; compressed source bytes `B = Θ(N log N)` | `O(N² log N)` total logical work (`O(B²)` coarsely) is the ordinary-ring target before production cutover, not a certified current bound. The structural derivation assumes SCC work `O(N log N)` plus identifier-byte cost, one guarded reentry per member, one initial R candidate and at most two shrinking rounds, `O(N)` replay/analysis per member without branching path expansion, staged drafts `D = Θ(N²)`, descriptor words `W = O(D)`, and prescribed §36 comparisons up to `O(N² log N)` across height groups. The architect and phase owners must prove the reentry/replay and `Normalizer::rank_all` selected-node/height-group premises and bring any remaining product tradeoff to the user for approval. Observed work is 3,031 / 9,256 / 35,245 / 149,517 for `N=2/4/8/16`, with a 4.24x rise from 8 to 16; those four samples do not prove a degree |
| `independent_identities(D)`, `identity_aliases(U)` | `D` identities, `U` aliases | `O(D)` and `O(U)` respectively; alias instantiation work is independent of unrelated arena size |
| `shared_acyclic(D,K)`, `independent_acyclic(D,K)`, `guarded_cycle(D,K)` | `D` roots, compact cone size `K`; separately count path-expanded occurrences and replay visits | derive separate producer/summary, candidate-mask, R-round, replay, materialization, and finalization terms from each builder's actual dimensions. The exact §34 summary-hit and uncacheable-state counts remain required; no total-work order is asserted here |
| `normalization(D,K)` | `D` members, key/child width `K` | `O(N + W + C_norm)` with the exact prescribed comparison schedule |
| `arena_factor(M,U)` | `M` unrelated arena nodes, `U` uses | `O(M + U)` for construction and `O(U)` for the use path, independent of `M` for per-use substitution |

For the SCC-ring and acyclic/cyclic graph families, the source-level proof must
account separately for root count, each candidate-mask version, every R round
(at most `r+1` for `r` initial candidates), and path/trace multiplicity. It
must identify materialized occurrence count, not relabel that count as compact
input size. The SCC-ring objective applies to that ordinary compressed-source
family and does not extend to all adversarial path-sensitive contexts.
Path-sensitive reentry is order-observable; the current review does not prove a
polynomial bound for all such contexts. Those pathological
contexts are not rejected at a selected size/work threshold and may continue
until runtime resources fail. Any later change to exact public counter meaning
or R/Q ordering requires a separate reviewed addendum and user approval.

Path-sensitive reentry remains ordered by first-surviving trace, with existing
Q/R eligibility, binder order, and exact counter meanings. A future change to
share those paths or reinterpret counters requires a separate narrow design
amendment and approval; this addendum does not silently change that contract.

## 4. Evidence and production gate

The completed source-Lambda capture and §15 plan are historical evidence only;
their capture budget is exhausted. Do not repeat or extend those captures.
Before any new resource, scale, or capacity probe, prepare a fresh bounded plan
for the new decision under `rules/performance.md`, including the exact ordinary
families above, distinguishable sizes, dimensions and expected formulas,
commands, process/wall-time budget, stop rules, and failure/retry coverage.
The F5 §26 identity, alias-use, shared-graph, and arena-factorization runs at
1k/2k/4k remain required, with their exact causal counters and adjacent
actual-capacity/retained/peak observation ratios `<2.5`. Their per-run
30/60/120-second timeouts protect the isolated measurement harness; they are
not F5c input or compiler runtime cutoffs. Any measurement plan must fit the
ordinary 8-process/10-minute budget in `rules/performance.md`, or obtain its
required written performance-auditor justification and primary approval before
execution; a plan exceeding 16 processes or 20 minutes also needs user
approval. These requirements must be reconciled before scheduling the runs.

Before production selection, independently audit every producer/materializer/
normalizer/finalizer allocation and return/error edge; verify stack-independent
success, error cleanup, and ordinary drop; reconcile all source/finalizer
co-resident physical lanes; preserve exact counter/parity witnesses; and close
the reviewed ordinary-family complexity evidence. A separate reviewed
production/API cutover and recorded user approval remain required. F5e remains
outside this gate.

## 5. Supersession and open implementation evidence

This addendum supersedes only the forward-looking numeric
admission and production-gate requirements in these scopes:

- Flat indexed candidate §5's configured draft-size and repeat-work ceilings,
  including its statements that the meter stops path amplification and that
  workloads must be measured to select a supported numeric boundary. The
  charge-site definitions, checked work observation, physical ledger, and
  checked pre-growth censuses remain.
- Flat indexed candidate §§7–8's numeric admission/boundary closure criteria,
  §13's numeric-boundary selection objective, §15's requirement to select a
  numeric supported boundary before cutover, and §§17/20's requirements to
  implement numeric size/work admissions before production connection.
- The forward-looking production-blocker status in shared-walker flat-sink
  §§3 and 9 and its latest status that ties production cutover to a numeric
  boundary. Its rollback ownership, exact operation counters, and resource
  observation requirements remain.
- The `rules/design-authority.md` bounded-envelope preference only within
  F5c scope. No other feature's resource boundary is changed.

Earlier review reports, probe history, and completed checkpoints remain
historical evidence; this addendum does not rewrite them.

It does not supersede flat ownership, stack independence, checked arithmetic,
fallible returned-error handling, exact counters, Q/R and normalization order,
physical capacity reconciliation, failure-epoch behavior, atomic publication,
Oracle parity, or the separate production cutover approval.

The current candidate's all-input complexity is not certified. Known path
expansion and root/mask/reentry work must be recorded honestly in terms of the
expanded dimensions. The no-cap policy permits those costs to continue until
ordinary runtime resources are exhausted; it does not claim that pathological
inputs are practical, fast, or guaranteed to complete. Production acceptance
requires a source-level complexity proof for each ordinary family above plus
independent confirmation that selected physical-capacity samples match the
per-lane ledger. Samples alone cannot substitute for the phase formulas.
