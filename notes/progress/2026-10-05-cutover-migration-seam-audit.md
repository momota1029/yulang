# Inference cutover: production ownership and migration seam audit

Date: 2026-10-05. Baseline: `dfd49d1b14a9aba922bb0278ca7c1bfac8061058`.
Branch: `research/simple-sub-intrusion`.
Status: unreviewed research characterization; no implementation authority.
Method: pinned source call graph and ownership analysis, compared with the
public API disposition inventory. No production edits, builds, tests, or
measurements.

## Result and exact scope

The existing private **whole-attempt `InferenceSession` behind
`SolvedModule::solve(ConstraintBatch)`** is the smallest existing ownership
boundary that encloses the complete inference replacement while keeping
public collection and frozen-result observations at its edges. It is an
existing private owner, not a generic backend or newly approved interface.
Inside it, SCC execution, generalization, incoming-use realization, live
value/effect constraints, diagnostics, and finish projections share state.
No smaller existing seam has an established contract sufficient to substitute
the successor while preserving all those downstream observations.

No independently approved **production inference cutover slice** is ready at
this baseline. The precise blockers are source-generated root/local/anchor
classification and full-bound adequacy, soundness/principality for a stated
envelope, and the successor representation/compatibility approval gate.
These blockers exist even without deciding the pending Function-inlet context
question. This finding does not prohibit a mechanical refactor or more
authorized isolated research; it establishes no impossibility theorem about
future modular implementations.

## Frozen inputs and authority

The read-only inventory
`notes/progress/2026-10-05-inference-cutover-api-disposition.md` declares baseline
`a674fcf72`, not this audit's baseline. Its SHA256 when inspected was
`5c3ba7732fa0547b18eb6d79535ac2e5f0a57265ce1efa4cd876d9a40b157b05`.
`git diff --name-only a674fcf72 dfd49d1b1 -- crates tools Cargo.toml Cargo.lock`
returned no paths. Therefore its source locators and workspace-consumer search
remain source-compatible with this baseline. Its independently reviewed
inventory is reused as coverage evidence; this audit does not reproduce counts
or inherit its independent-review status. Dirty shared task/design/theory files
and unintegrated question answers are not inputs or authority.

Governing sources read:

- `rules/design-authority.md` and `rules/research-lab.md`.
- Committed `tasks/current.md`, Objective/authority, Closed decisions and
  source/solver bridge boundaries; committed design index for navigation.
- SCC-intrusion redesign charter §§1–6: F5 internals are replacement material;
  final supported well-typed capability is the compatibility target;
  soundness/principality precede representation and approval.
- Authoritative static SCC inference-session design §§2–5: private concrete
  ownership, live internal uses, all-member visibility barrier and
  whole-attempt failure.
- Authoritative experimental transport gate, Bounded implementation gate,
  Owner/entrypoint and Next gate: `cfg(test)` identity transport only.
- Authoritative cross-edit rebuild addendum, Interface comparison boundary
  and Compatibility/gate: complete interface and equality remain open.
- Authoritative F5c no-numeric-caps addendum §4: removing numeric-cap selection
  did not approve production/API cutover.

The charter does not require preservation of F5-specific Q/R, closed-scheme
alpha form, or F5c resource/API architecture. A later cutover may record
intentional compatibility deltas. The current exported observations identified
by the inventory still require an explicit disposition; this audit does not
freeze them as the successor's semantic or representation target.

## Production call graph and ownership

All `L` locators below mean pinned `crates/yu-solver/src/lib.rs`.

```text
SolvedModule::solve(batch)                         L15665
  InferenceSession::try_new(batch)                 L9178
    collected Term lineage -> session store        L9205
  InferenceSession::run()                          L9731
    admit_all_collected_facts()                    L10447
      admit_lambda_fact() -> Function + live bound L10539
    execute_scc_plan()                             L12874
      dependency-first component loop              L12978
      route_internal() -> live root/use edge       L13985
      all-member component_generalization_draft()  L13095 / L15162
      finalize_generalization_draft()              L13277 / L15187
      install every finalized member               L13905
      route_incoming() -> fresh closed realization L14674
    store.finish_accounting()                     L9735
    finish()                                      L15419
      live value/effect projections               L15424
      fallible closed-owner finish                L15504
      frozen SolvedModule publication              L15639
```

`ConstraintBatch` owns immutable HIR/source identities, recipes, collected
Terms and the SCC plan (`L762` onward). `InferenceSession` owns their live
translation, bound rows, level/non-generic metadata, typed memo/worklist,
diagnostic and route journals, closed finalization and scheme slots (`L7200`
onward). Startup transfers the collected lineage to its store instead of
rebuilding public handles (`L9205`). The frozen result contains both the
retained store and closed schemes/arena (`L7168`); it is not just a root type
summary.

The source-visible flow crosses each candidate smaller seam:

| Candidate seam | Actual crossing dependency | Consequence |
|---|---|---|
| Value-only constraint kernel | `constrain_live_value` delegates to one typed memo/worklist containing effect tasks (`L11047–L11084`); Function children carry four ports (`L12308–L12340`) | Splitting off a pure value solver does not establish preservation of coupled Function constraints, diagnostic completion or shared rollback. |
| One member generalizer | Generalizer reads the whole session and frozen component epoch (`L15162–L15184`); all member drafts precede finalization and incoming uses (`L13095`, `L13253`, `L13905`) | A root-only return value lacks the existing component visibility and bound/evidence context. |
| One completed SCC | Incoming uses instantiate the installed closed scheme into fresh live rows and route facts back into the same attempt (`L14527`, `L14674`, `L13966`) | An SCC is a scheduling/quantification boundary; no independent successor component carrier or compatibility adapter is supplied. |
| Finalization alone | Existing function takes F5 `GeneralizationDraft` and emits `ClosedValueScheme` into a shared finalization owner (`L15187`); incoming uses consume that algebra (`L14199`, `L14527`) | Replacing a finalizer implementation can preserve its existing algebra, but that operation does not replace F5 inference or give intrusion a compatible outgoing interface. |
| `finish` or result summary | Occurrence projection reads live rows (`L15424`); root query reads finalized closed schemes (`L15708`); retained store and errors move separately (`L15639`) | Projection parity alone omits observable terms/facts/provenance/errors and the hidden constraints consumed before finish. |

The public store also does not delimit complete downstream inference semantics:
the route comment at `L14192–L14196` explicitly separates admission of the live
representative edge from publication of the one public source projection.
The inventory's §44 analysis records other normalized members as private.
Likewise, `root_value_for` maps quantified/recursive/Function/Union predicates
to `Unknown` (`L15737–L15748`). Equal public projections or fact summaries do
not prove equality of the complete generalized interface.

## What can already proceed independently

Finite identity-only transport has its own approved research boundary:
`mod intrusion_transport` is `cfg(test)` (`L211–L212`). The gate supplies its
graph, root, ordered bounds and complete disjoint identity partition as inputs;
it does not derive them from production source or select their semantics.
Its next gate explicitly names source-generated member/root classification
and full-bound adequacy. The existing implementation and focused follow-up
are recorded complete at this baseline; this audit supplies no newly needed
implementation subtask within that already-completed gate.

The older flat F5c candidate does not provide an alternate production cutover:
the switch is a test-only field (`L7300–L7301`), and production unconditionally
executes `boxed_component!()` (`L13883–L13884`). Its completed staged work is
candidate evidence. The no-numeric-caps addendum §4 still requires a separate
reviewed production/API cutover and recorded approval. Connecting either
candidate to production would cross its explicit gate.

The cross-edit addendum permits rebuilding a changed inference component but
does not identify that component with an existing F2 SCC or expose a reusable
interface. Its unresolved interface fields, equality, dependencies and
enclosing-environment/SCC-change cases prevent using it as an independently
approved cache or migration adapter. No editor/cache path is selected here.

## Preservation obligations and next evidence

A future proposal can start at the existing whole-attempt owner while retaining
collection and result wrappers. It must explicitly retain or approve changes to
the inventory's exported observations: artifact/Term lineage and lifetime,
total ordered occurrence queries, exact-versus-unknown projections, ordinary
Never, local diagnostics and canonical causes/order, fact/provenance identity,
query and resource counter meanings, and no partial result on availability
failure. It must separately prove source adequacy and principality; tests of
those observations cannot supply that proof.

The next useful cutover artifact is a source-grounded producer/consumer
contract for **one SCC's generalized output plus its enclosing live context**:
which roots and local/fixed identities it contains, which original directed
bounds/effects/evidence survive, how a fresh incoming use consumes them, and
what the consumer is allowed to observe. Prove the source bridge and exact
supported envelope before selecting production data structures. This is a
proof/contract recommendation, not an approved representation decision. It
can be pursued without consuming the pending inlet-context answer; any
Function-context-dependent extension must await that approved input.

## Checks, limits and commit packet

Checks: pinned `git show` source/authority reads; empty source delta from the
inventory baseline; narrow line-locator validation;
`git diff --no-index --check /dev/null <leased path>` emitted no whitespace
diagnostics (exit 1 identifies the new-file difference). Builds/tests/measurements:
none (budget zero). No external consumer
search beyond the inventory, full Oracle re-audit, execution, benchmark or
semantic compatibility certification was performed. Current passing tests
are cited only as inventory evidence, not rerun or claimed as proof.

Exclusive changed path:
`notes/progress/2026-10-05-cutover-migration-seam-audit.md`.
Research checkpoint status: unreviewed characterization, ready for primary
scope/dependency adjudication; independent review remains separate.
Suggested commit: `research: audit production inference cutover ownership seam`.
Shared `tasks/current.md`, theory/design index/status and pending questions are
intentionally deferred to the primary's integration lane. No Git mutation was
performed by this producer.

Pinned Git blob dependencies:

- `crates/yu-solver/src/lib.rs`: `fa118b726ebbfdc7d32b617373b4e2cb04e84682`.
- `crates/yu-solver/src/term.rs`: `001ffd3022b2fad0d7d67e0a853aaeb83db00b12`.
- `crates/yu-solver/src/scc.rs`: `945baf7dc2d59e74616f549f28703ef7a84f5eed`.
- `tasks/current.md`: `b70218b7a536d3e470d8ec2bd57f61f73ebd2791`.
- Experimental transport design: `788d0a1616959c58992d3ef25f134560c559f142`.
- Cross-edit rebuild addendum: `da96e6869e360f8bdf32e96668bcbce3e2d60f31`.

Recheck the inventory SHA256 before integration. If a dependency changes,
revisit only the affected source/authority conclusion; dirty unrelated records
do not establish a new baseline.
