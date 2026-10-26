# Next decisive inference packet: construct the canonical row solution

Date: 2026-10-26. Producer: `/root/native_soundness_dispatch`.
Assigned baseline: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, `yulang3`.
Selection only; no theorem, independent review, live assignment or gate promotion.

## Decision

Select **finite saturated row constraints -> one constructed regular solution**,
paired with an independent **complete physical-bound/replay extraction** lane.
Do not add another theorem taking a graph, row interpretation and successful
terminal decision as inputs. The next result must construct the graph and row
map, and derive terminal decision success from explicit syntactic saturation.

The unchanged parent is `Contracts.SourceProblem.InferenceSoundness` plus its
separate `NativeCorrespondence` supplier: every original supported generated
solution reconstructs the original source judgment with the same scoped witness;
actual native success must produce that complete solution. Source Call, effects,
optional records, method selection, hygiene, all uses and futures stay in scope.
The packet below closes a structural construction premise, not that parent.

## Primary evidence controlling the choice

* `candidate_extrusion.rs:1118-1179` stores a row inequality on **one physical
  side**, selected partly by levels. Therefore a row's
  `direct_lower_rows` alone does not enumerate its semantic predecessors.
  `a <: b` may exist only in `a.direct_upper_rows`.
* `candidate_insert_bound_with_evidence` at 702-874 owns all eight physical
  lanes, exact `PhysicalBoundSlot`, admission and immediate readback.
  `candidate_opposite_count`/`candidate_opposite_bound` at 877-935 give the
  direct-row-then-structural ordering. This is the correct extraction seam.
* `candidate_intrusion.rs:599-705` copies both sides before redirecting the
  representative and replays lower/upper pairs afterwards. Both old physical
  storage and canonical representatives must be retained by the adapter.
  `recapture_candidate_extrusion` at 388-420 can activate a group through later
  reuse while leaving `Parent.sources` immutable; original sources alone do
  not qualify every merge.
* Replay is richer than a set of endpoint pairs. `candidate_context.rs:126-151`
  retains ordered inputs, heads/prior, child relation identities, queued and
  consumed frontiers, retirement and child waiting state. The owner at
  `3992` composes source/context/scope fibers. Resumable restoration at
  `candidate_extrusion.rs:1000-1068` uses a saved count and live canonical reads.
* `Capture::expand_row` at `candidate_scheme.rs:2137` stops below shared owners.
  Its graph is not the complete store. Fresh use at 4199 and 4248 onward uses
  one actual canonical-row map and rechecks level/non-generic metadata.
* `Lattice.Node` has union/intersection but no alias constructor; guardedness
  forbids lattice-only cycles. `Regular.Node` preserves all four Function
  ports but its record relation currently preserves exact shape.
* `candidate_call.rs:137-147,397-435` retains scalar interfaces and still names
  original GenCall0, whole-argument and complete receiver/result/future suppliers.
  Native `Ok` cannot supply those fields by renaming it a full solution.

## Constructive proof lane

Proposed single multi-stage output: `SimpleSubSaturatedRows.lean`.

Start with a finite raw table of kinded rows, rigid structural endpoints and
oriented inequalities. This is a representation of retained constraints, not a
new source typing judgment. Normalize **all** lower and upper physical lanes:
lower slot `(r,t)` gives `t <: r`; upper slot gives `r <: t`. Quotient only the
actual union-find equalities. Then compute directed row-to-row reachability
from inequalities recorded on either side.

For canonical row `r`, define `Heads(r)` as the finite set of non-row lower
endpoints reaching `r` through zero or more oriented row inequalities. Construct
one graph root for `r` as a fixed finite union tree of translated `Heads(r)`;
use bottom for the empty set. Translate structural children through the SAME
row map in every position, including both negative Function ports. Pure row
cycles are removed by finite reachability; recurrence under Function, Tuple,
Record or Variant constructors remains as genuine guarded graph recurrence.
Do not use separate positive/negative assignments or independently chosen
solutions at different depths: these would lose correlation and the witness.

Proposed theorem target, with names finalized by its producer:

```text
finite well-formed raw row/constructor tables
+ every retained and original terminal demand is represented
+ explicit finite syntactic saturation/decomposition evidence
  -> let (graph, refs, demands) := constructRows raw
     graph.Valid /\ graph.Guarded
     /\ LatticeDecision.decideDemands graph demands = true
     /\ every raw inequality holds under the same refs
```

The saturation premise must be a concrete finite condition: each row-chain
head/upper pair occurs in the comparison table; each rigid comparison either
has an actual matching leaf/top/bottom case or emits its exact ordered child
comparisons. The Function child directions are `(-,-,+,+)`. It must not contain
`RegularSub`, `StoreSatisfied`, a successful graph decision, a valuation, a
terminal source typing or a generic assumed preservation law. Prove every
generated pair sound at every finite depth by induction on depth with finite
join derivations, then use the existing exact decision theorem. This supplies
the missing accepting certificate constructively without a production pass.

First prove extraction-independent row reachability and join construction;
then integrate concrete constructors already represented by the current
graph semantics. The native inventory lane must list every remaining actual
constructor and its missing rule. Do not silently map contextual effects to
opaque equal atoms, discard optional/width cases, or report this as closure of
the full native domain. A missing native structural rule is an extension
obligation with its original owner, not permission to reject its source.

**Discriminator:** reject the plan if an explicit saturated raw table cannot
receive this shared interpretation. In particular, inspect a row edge stored
only as an upper, a pure row cycle with no rigid lower, guarded negative
recursion through a Function argument, repeated use of the same row in all
four ports, and a rigid incompatibility. These are finite proof examples, not
random source scans. A synthetic failing table refutes this construction only;
native unsoundness requires an actual original source/native witness.

## Independent native correspondence lane

Construct the lossless finite inventory first, before requesting any experiment.
Enumerate every physical slot by row, kind, lane and index; retain its raw
owner/endpoint, final representatives and emission/readback identity where
present. Keep both copied source slots and destination slots, exact transport
`parent_index`, and original AND later activation records. Preserve all
constructor payloads, record optional bits, tuple offsets/order, variant tags,
and each contextual effect operand rather than projecting them away.

For every demanded comparison, connect its actual relation/context/scope ID
to replay children and completion generation. Restoration evidence must retain
the saved bound count, each live read and child return; an empty worklist is
not a substitute. Audit whether every physical write actually traverses the
evidence owner; if not, identify the exact bypass and its needed constructor
receipt. This lane proves/records syntactic coverage and saturation at the
real owner, independently of the semantic join construction.

Initial native deliverable can be an exact extraction function and owner proof
in a research artifact, with no production call site. Any test-only Rust
instrumentation is a subsequent exact primary grant, not implied by this
selection. No additional seven-fixture-style scan is useful. If a missing
retained datum makes a finite experiment indispensable, specify the operation
and falsifier first; at most one focused 120-second Cargo run, one job/thread,
with a separately granted scratch/cache lease. No production checking pass.

The first cross-lane integration seam is a frozen table schema whose two
directions are explicit: every physical slot maps to a constraint and every
required comparison is represented by actual operation evidence. Run the
constructed row solution on that schema, then connect it to existing history
reflection. A final canonical interpretation is often simpler than pretending
native representative mutation is literal graph append. Reuse a fixed-final-
graph history when justified; do not assert the existing growing theorem
already proves that translation. Publication still needs its actual allocation,
stopping and scope invariants; numeric min/OR alone does not supply them.

## Why this route, and what remains blocked

Directly extracting an arbitrary graph and asking the existing finite decision
procedure whether it succeeds leaves both row interpretation and native-success
acceptance unproved. The finite reachability/join construction reduces both
premises at once. It is the concrete neighboring-method contribution: eliminate
epsilon-like row edges by finite reachability, retain constructor-guarded cycles,
and derive the regular model by depth induction. Applicability is checked by
actual local decomposition evidence, not by assuming semantic satisfiability.

Full original source reconstruction is a useful later integration, but it is
not presently a stronger ready replacement packet. Full `G_call` already
contains its certificate; local inversion may consume it. The reviewed original
Call evidence handoff leaves the actual certificate telescope/interpretation
binding unadopted, and native suppliers remain absent. Selecting copied-field
equations as the real host's independently fixed predicates would be a semantic
decision. No such choice is needed for the proposed row construction. If the
Call producer is resumed, resolve the exact field/interpretation binding at
its original authority rather than adding a needless all-model theorem or
another opaque `LocalLaws` parameter.

## Proposed leases, budgets and integration

These are recommendations; only the primary grants them after checking live
ownership. Foreign UNKNOWN/R63 reservations remain quarantined. Do not write
`current.json`, `YulangClosure.lean` or any reserved R63 path.

* Proof: only new `notes/theory/lean/YulangClosure/SimpleSubSaturatedRows.lean`
  and `tasks/agent-loop/inbox/20261026-inference-saturated-rows.md`; isolated
  scratch `/workspace/scratch/f98087c7ac1a/inference-saturated-rows/`.
  Budget 1,800 seconds, at most six focused Lean invocations at 120 seconds,
  pinned toolchain, one thread/1 GiB, complete originating-declaration audit.
  No children or assumed custom-role/model identity.
* Native: only new `notes/theory/2026-10-26-native-bound-inventory-construction.md`
  and `tasks/agent-loop/inbox/20261026-inference-native-bound-inventory.md`.
  Budget 900 seconds, initially zero compiler/checker runs. A runnable exporter
  needs an explicit additional exact file/cache grant after its schema freeze.
* One fresh nonauthor review of the coherent theorem and its owner map; reject
  semantic premises disguised as saturation or missing lanes/activation cases.
  Primary integrates imports/audit/navigation, then makes small coherent commits
  and pushes under the existing user authorization. The review does not certify
  unproved original Call, source, publication or production gates.

Consult again only for a counterexample, an actual missing semantic definition,
the frozen schema integration seam, or budget exhaustion. No new user decision
is needed to start this unchanged-scope proof packet. The exact original Call
interpretation decision remains localized to that separate producer.

## Cessation

Only this receipt was written. No Git, source/checker/cache edits, tests,
experiments, children, scheduling changes or status promotions. Governing
operating maps, next-action skill, goal-driven rules, design authority,
original inference principles, latest frozen evidence and actual named code
owners were read. All writes stop with this receipt.
