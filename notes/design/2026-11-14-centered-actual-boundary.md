# Explicit centers at the actual-inspection boundary

Status: additive representation and transition kernel, with checked partial
bridges. This is not a completed B4 implementation or an unconditional
simulation of the repaired actual-inspection relation.

## Authority and meaning

The owner chose option 2 in [spec §6.5](../../spec/06-roles.md), recorded in
[B4 addendum 8](2026-11-08-b4-main-statement-draft.md) and inbox I-29:

> 実際の引数の名前（中心）は明示して持つ

> 中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない。

> role の解決（候補の照合、曖昧、K2）は今までどおり区間の端点と既知の頭で行う。

> 実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない

The nested decision dated November 14 governs the older November 8 sentence
about intervals without centers. It retains the interval resolution rule while
adding names for actual arguments. No further owner question is needed here.

The earlier decisions still apply: all unnamed input heads must be known
(addendum 4), and outputs of unfinished obligations cannot justify expansion
(addenda 5–7). Such equations can still contribute to ordinary equality and
K2. Root unknownness has the exceptional priority in addendum 1; after it,
root/candidate K2 precedes pending inspection, ambiguity, and selection.

## Representation and lifecycle

`GeneralNominalCenters.Argument` contains `(endpoints, center)`. `center : Nat`
is a source identity interpreted by the existing general-carrier assignment;
it is not a finite type expression or a selected value. Its model condition is
`Fits model endpoints (model center).1`. Recursive and infinite types remain
in the carrier. `NominalArgument` additionally connects an actual observation
path to its center, using semantic equality in both directions.

A centered demand site stores its original occurrence and one center for each
unnamed argument. Named outputs retain their existing source identities. The
legacy occurrence, interval endpoints, candidate syntax, registry identities,
and canonical child occurrence allocation remain intact.

| Stage | Center representation and constraint |
| --- | --- |
| Initial source | `rootSite` gives every root input a name. If the endpoints have the same identity, that identity is the center. Otherwise allocation purpose 7 creates a name above the source seed. |
| Capture | `Plan.binder` reuses a point capture's identity, retains output-only binder identities, and uses purpose 8 for a nonpoint input binder. All actual head uses of one variable are equated to this one binder center. |
| Emission | A bare variable forwards that binder center. A compound gets a purpose-9 name indexed by invocation, declaration, clause, and argument position, together with an actual-mode materialization request. |
| Materialization | `SchemaHolds` reads tests as general-carrier observations. Every actual-mode variable use equals its binder center; lower/upper uses retain the original endpoint interpretation. Input, named-output, head, and compound-child schemas are retained in `Plan.Equations`. |
| Installation | The legacy ordinary journal is updated by the existing shared emitter. A separate ledger appends all centered child sites and retains the plan equations. `install_models` characterizes the resulting model set exactly. |
| Recovery/refresh | Center recovery is identity on the center site. Administrative updates retain the ledger. The new `Refresh` certificate can use the centered model set to justify a refined endpoint view, while retaining the existing source-support and known-head improvement conditions. |
| Merging | `SameInputs` compares total source-center observations under centered models. Equal numeric names suffice; different names require a proof of equivalent actual values. Merging retains both center records. |

`initialAt` accepts an explicit centered root site, and `InitialSource` requires
that point centers equal their point identities. This interface can preserve
preexisting sharing between two root positions. The default `rootSite` names
nonpoint positions independently: it cannot reconstruct actual-argument sharing
from equal endpoint pairs. A source producer must supply the shared name or its
equality constraint when such sharing is present; that producer bridge remains
open.

Purpose tags use the existing injective origin encoding and persistent seed;
registry order is not an allocation input. A nonpoint root center is proved
fresh relative to the seed. This patch does not prove a global collision and
model-extension invariant for all new allocations.

`Site.observed` has no missing entries. `capture_agreement` proves that actual
head uses refer to the shared binder; `input_coherence` does the same for
actual-mode input uses. `generation_guard` constructs a centered usable
certificate for every needed variable from those equations and its binder
bounds. Consequently `ProvenanceGap` is empty for every centered plan, without
a head-readiness assumption. Head readiness remains an independent expansion
condition; having a center does not make an unknown head known.

`GeneralNominalCenteredSupport` also removes the indirect raw-capture blocker
in output promotion. Its finite trusted history rechecks input observations
against the preceding facts, adds input equations without the named-output
schema, and promotes named equations only when that exact packet is settled.
`outputCertificate` supplies a uniform substitution of explicit binder centers;
`output_readback` proves its recipe interpretation. It does not ask for an
optional raw capture. Centered same-input merge facts have their own trusted
rule. An optional legacy history constructor reuses already valid old proofs.
The recipe substitution includes named output-only centers as leaves; it does
not transfer the old theorem restricting leaves to input origins and earlier
readbacks. No old descent result is inferred from this readback lemma.
Source centers are stored separately and retained across updates, so emitted
sites are not treated as original source facts.

The checked W fixture now has this centered output certificate despite the old
`SharedPump.leaf_output_deferred` obstruction. Readback and settlement premises
still have to be produced by an execution; the total certificate alone is not
an installation or output-promotion trace.

These statements concern **centered packet models**. They do not establish the
old `SharedCaptures.Captured` predicate under raw `Packet.Holds`. That predicate
reads raw site origins, whereas `Packet.Holds` ignores them. Strengthening a
separate model set cannot prove a claim quantified over every raw branch model.

The implementation is an overlay at demand sites, capture binders, and emitted
arguments. The generic `NominalArgument` record describes nested invariant
arguments, but the frozen native nominal descriptor has not been replaced and
its recursive producer/consumer integration is still open.

## Centered transition and local predicates

`GeneralNominalCenteredSteps.State` contains the legacy tracked state, centered
sites, and retained plans. Its `Step` has administrative, centered-refresh,
installation, and same-input merge actions. Installation uses the existing
ordinary installability checks and legacy value support, new centered settled-head support, and centered actual
inspection safety, safety of alternatives, exclusion of root/candidate center
cycles, and a model witness for the centered branch. It does not test for a
missing shared-provenance certificate.

`GeneralNominalCenteredGraph` reads a finite list of actual-mode head, named,
and compound-child tests. Each structural or explicit nominal argument edge
comes from a recorded constructor test. Model equality can transport an edge;
it cannot create one without such a test. A cycle also requires an inhabited
centered model set. `graph_tests_hold` proves that the recorded tests hold in
every centered model. The graph is combined with the frozen actual-position
graph. Nominal bodies supply no edges.

`GeneralNominalCenteredBoundary` keeps endpoint survivors and endpoint
unknown-head/inspection diagnostics, uses centered settled support, adds root
and inspected center cycles, and adds **no provenance or residual-availability
pending rule**.
The checked statements include:

- Local functionality and totality, and the prescribed K2 priority.
- Installation enabled by the centered guard implies local selection.
- The exact pending formula, with the retained old inspection predicate
  visible; completeness of that old predicate is not asserted. Its inherited
  compilation checks include freshness, preparation, and request readiness;
  the formula is not claimed to equal only the owner-authorized lazy cases.
- Exact survivor equality with the prior empty-gap adapter.
- Full local correspondence to that adapter when additional root-center cycles
  are absent, candidate-cycle and decision-support predicates coincide, and
  its old `Blocked` predicate is false.
- The six V5 fields `closure`, `stepModels`, `frontierLocal`, `localIdentity`,
  `dictionaryRefl`, and `initialReorders`, for the new centered `Step` itself.

Selection implying installation or prior installation remains unproved.
In particular, the centered branch model witness and the old ordinary
preparation/support checks have not been derived from the local predicates.
Their failure is an implementation completeness gap, not an additional
language-level pending case. The previous adapter with `ProvenanceGap = False`
still contains `ResidualGap = Blocked`; merely selecting that parameter value
would violate the purpose of the new owner decision.

## Trigger and positive examples

Write `V t` for `:tick t`. In the owner's example:

```yulang
impl W (:{tick 'a}) 'b:
    type anchor = 'a
    type out = :{tick 'b}
impl P (:{tick :{tick 'a}}) 'b:
    where (:{tick 'a}): W('b, anchor = 'z, out = 'z)
    where (:{tick 'a}): P('b)
my trigger(x: 'a, b: :{tick 't}) = (:tick (:tick x)).pump b
```

Both children carry the same center for `b`. The first W gives `A = V b`.
The next matching step reads `A = V next`, and its W gives `next = V b`.
Variant cancellation yields `b = V b`. The recorded `V` output edge has its
child equated to `b`; transporting the parent equality therefore produces a
nonempty self-cycle at `b`. At a known root this is K2 rejection, even when
other predicates would defer inspection. It is never a provenance-pending case.

The Lean fixture uses the existing checked P/W declarations (which also retain
an auxiliary `tail` equation). It proves that the two emitted children share
`b`'s center, that the root nonpoint center is named, that head materialization
connects it to the binder center, and that centered generation succeeds while
the old generation certificate is absent.

`trigger_k2` and `trigger_rejected_of_trace_constraints` formalize the cycle and
local rejection **assuming** the three produced equations, recorded edge,
shared child, and model witness. No reachable centered trace producing all of
these premises has been constructed. This note's operational explanation is
the required intended execution, not a claim that this missing trace is proved.

For Display and Wrap, the initial centers equal their point source identities;
their initial model sets and local selected outcomes are proved unchanged.
For the branching Show source, its initial model set and inhabited witness are
proved unchanged. Endpoint survivor sets are unchanged generally. Preservation
of the complete positive executions, including the branching Show selection
and every emitted descendant's centered guards, remains open.

## Simulation, audit, and remaining bridge work

`CompatibleStep` is explicitly the intersection of centered `Step` with an
actual-inspection step between erasures. Exact erasure and guarded action-level
lifts are proved. `RawPacketCompatibility` lists the old settled decision, raw
capture, input-coherence, and actual-position obligations for installation;
refresh and merging expose their raw-model/registration obligations separately. The existing ground point-root accessibility
result transfers to **this intersection**, and terminal execution existence
follows there. The unrestricted centered kernel only has terminal existence
conditional on its own supplied accessibility proof. No new descent proof is
attempted.

The missing unrestricted simulation is substantive: a centered installation
can use equations that raw `Packet.Holds` does not retain; a centered refresh
can use facts unavailable in erased journal models; and merging may use
center equality absent from raw sites. Point initial models coincide, but a
point-root preservation theorem discharging those differences after every
update is still needed before claiming the requested ground-root transfer.

The next additive bridges are:

1. Produce the centered trusted input/readback and refresh certificates from
   actual source states, and bridge centered head support to the retained
   legacy value guard. The centered output recipe constructor is already
   provided, but this remaining installation guard can still block a step.
2. Prove allocation/model-extension and nested nominal-center invariants.
3. Derive centered guard availability from selected reachable local states.
4. Construct the P/W trigger trace and its inhabited final graph; preserve
   the full positive executions.
5. Prove the point-root simulation or an equally strong connection to the
   existing actual-inspection theorem; then transfer the remaining B4 fields.

No registered prover launch surface was available. The primary constructed
these bounded proofs and a separate read-only agent reviewed them. New proof
dependencies are checked in `lean/Audit/CenteredBoundary.lean`; this does not
certify any of the open source or execution bridges above.

## Validation

Final commands, run from `lean/`:

```text
lake build Yulang.GeneralNominalCenters Yulang.GeneralNominalCenteredGraph Yulang.GeneralNominalCenteredSupport Yulang.GeneralNominalCenteredSteps Yulang.GeneralNominalCenteredBoundary Yulang.GeneralNominalCenteredExamples
# exit 0
lake build Yulang
# exit 0, 2331 jobs
lake env lean Audit/CenteredBoundary.lean
# exit 0, 84 theorem declarations
```

The new audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The existing-file changes preserve the exact original byte prefixes of
`lean/Yulang.lean` and `notes/design/INDEX.md`. All six new modules are imported
from the aggregate module. No commit or reference mutation was performed.
