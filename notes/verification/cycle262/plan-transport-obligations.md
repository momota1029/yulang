# cycle262 Plan transport: proved structure and remaining obligations

Scope: output-body and EqualOutputs finite fact tables, not the complete packet,
head, capture, Evidence, or language resolver. Research and focused implementation
2026-11-18 18:47–18:52 UTC.

## Why fixed request coverage is not enough

SourceObserver262 supplies a source-derived fixed request pool and bounds finite
novelty-gated writes for observers returning snapshots reachable from that same
source. It does not constrain which Plan a caller uses at each observation. A
request's stable address records owner/request/equation index, not the meaning of
an arbitrary changing declaration, translated expression, or actual input center.
Thus a request-only novelty check could suppress a genuinely different obligation
if the meaning of its old address changed.

Dependencies read:
- BodyTable261 schema/variables/keys/localHolds;
- StableBody261.Holds and StableClass261.Holds;
- ClassTable261.Effects;
- VersionedEffects231.BodyHolds and actual_value;
- CenteredHeadMatEffects.compileBody/bodySchema/defaultVariables;
- Centers.Plan.binder and VersionedFrame231.binder_eq;
- VersionedInstall232.installCore and existing mixed-source public-port closure.

## Proved sufficient invariant (GeneralRebasePlanTransport262)

`Same first last` requires:
1. equal packet declarations;
2. equal packet registry constructor catalogues;
3. equal constructor interpretations;
4. equal actual `Plan.binder name` for every name;
5. equal `List.ofFn input.center`.

It does NOT require equal packets, contexts, ordinary journals, bounds, lower/upper
captures, observation histories, or models. It does not assume ClassEffects or
Holds equivalence as a field.

Derivation:
- equal declaration fixes body lookup;
- equal catalogue/interpretation fixes translated body schemas, including failure;
- every body-schema equation uses `.actual` mode;
- explicit body actual variables reduce to assignment of Plan.binder;
- default actual variables reduce to indexed input.center;
- actual_value transports evaluation, then every equation-table address meaning;
- pair equality facts are Plan-independent.

Consequently `facts_eq` gives exact table list equality and `stable_class_holds`
gives equivalence for every fact and assignment. `effects` and `class_effects`
follow for arbitrary request lists and source snapshots. Missing bodies and failed
translations keep the same empty/unknown schema; these proofs do not turn that
schema into Ready or acceptance.

`of_report_data` derives this invariant from existing
GeneralNominalCenteredHeadMatPlanData.Same. That older invariant fixes registry,
declaration, input, seed, state constructors, interpretation and erased report,
and already proves equal capture/binders. It allows ignored cache/history fields
to differ, but is not automatically available for changing captures.

## Nontrivial actual-plan family

GeneralRebasePlanTransportExamples262.changing_atoms uses the actual
GeneralRebaseMergeRequests261.candidate family with arbitrary two ordinary-atom
lists. Its zero-input declaration has empty bindings at both snapshots;
capture_seed gives capture equality and hence actual binder equality. These are
not assumed to be equal Plans or equal contexts. The family obtains exact tables,
all-fact meanings, and ClassEffects equivalence without Good, raw-model, or
satisfiability assumptions. This does not assert arbitrary atoms are source
reachable, or that a packet's raw model/Evidence transports.

## Capture changes that are structurally safe

GeneralRebaseBinderShape262.Compatible requires each non-output binder to be either:
- the same point source at both observations, or
- nonpoint at both observations (endpoints need not agree).

With equal seed, occurrence identity and declaration, public output names are
identical by the actual allocation definition. Both nonpoint inputs use the same
purpose8 fresh binder identity; both identical points use that point name.
`binders` derives actual binder identity, and `transport` discharges the binder
field of PlanTransport.Same. This is a sufficient family, not an invariant already
proved for every source transition. In particular nonpoint→point is excluded.

The existing GeneralNominalHeadTransport184.nonpoint_binder_eq proves a related
identity lemma; the new module packages the point/nonpoint disjunction and the
public-output case for use with the output-table theorem.

## Remaining source-level work

1. For an actual observed Plan at each new rebase state, prove Same with its fixed
   representative, or use a finer state/meaning design that permits changed bodies.
   Source request-pool coverage alone does not provide this.
2. Preserve the selected declaration and translation configuration along that
   Plan family. A different declaration with the same owner/request cannot be
   silently given the old fact meaning.
3. Derive actual binder/center transport across nonpoint→point changes. The existing
   GeneralNominalHeadSchemaSemantic186.binder_same establishes semantic binder
   agreement from semantic center agreement, both head SchemaHolds, and Finished;
   it does NOT give unconditional identity. Its premises must be supplied from a
   valid new-boundary model, not imported as if an old Step result covered rebase.
4. If semantic rather than syntactic binder/center equivalence is used, prove
   expression congruence and state clearly whether the result is conditional on a
   shared base/model predicate. The present all-assignment theorem uses identities.
5. Prove Ready/Frame/capture/packet conditions separately before claiming Evidence.
   Stable body equations are only part of packet semantics.

## Why arbitrary changing Plan cannot be presumed safe

Even with the same packet, Plan.input.center can be changed while retaining the
same occurrence and input_exact. A positional default `.var 0` then reads a
different source name. Under an assignment distinguishing those source names,
its output equation changes. This paragraph is a structural counterexample plan,
not a newly kernel-checked source-reachable counterexample. Similarly, nonpoint→
point can change purpose8 binder identity to a source endpoint. No universal
Plan-transport theorem is claimed without the explicit structural premises.

No whole compiler, old Step termination, arbitrary Plan acceptance, or automatic
source observer construction is established by this work.

## Semantic weakening added later in cycle262

GeneralRebasePlanSemantic262 separates structural Layout from assignment-specific
Compatible. Layout fixes only declaration, constructor catalogue and interpretation;
it already gives schema/key/fact list equality. Compatible additionally requires
semantic Equivalent actual binder values and positional default-center values at
ONE assignment, not identity of their source names. actual_value transports only
actual-mode expression evaluation using the existing expression-congruence theorem
with actual-fixed environments; no endpoint-mode agreement is needed. It then
proves per-fact Holds, BodyHolds, Effects and ClassEffects equivalence at that same
assignment. These are not unconditional all-assignment results.

GeneralRebasePlanSemanticExamples262 proves this weakening is strict when an input
position exists: shifting all center names by1 is not structural Same, but remains
semantically Compatible under any constant assignment. Body effects transport at
that assignment. This is an arbitrary Plan transformation demonstrating logical
scope, not a source transition or a proof of packet validity.

To use semantic transport during a changing-Plan run, each shared assignment must
satisfy the semantic compatibility premise at all selected observations. Showing
this from actual new-boundary models remains open. Layout alone can keep the fact
keys unchanged even when their meaning changes; it must not be used alone to claim
history-preserving semantic correctness or acceptance.

## Base-relative observer bridge

GeneralRebaseSemanticObserver262 reuses the actual-Plan proposals of
ObservedPlan262.observe. LayoutCompatible alone gives exact proposal table
identity and finite completion under request coverage. BaseCompatible requires
actual binder/positional-center semantic compatibility only under the unchanged
base assignment predicate, at selected roots of all finite states. It does not
assume whole output-effect equivalence.

write_actual and step_actual yield the exact actual observed Plan ClassEffects
for every assignment. Both sides include Models, whose first conjunct is base;
when base is false both sides are false. When base is true, the lower-level
semantic-variable premise supplies the output transport theorem. An empty base
is allowed but is not presented as language acceptance or satisfiability.

SemanticObserverProbe instantiates LayoutCompatible and BaseCompatible for
arbitrarily recentered Plans under a base selecting one constant assignment.
This is a genuine weakening of structural identity (see strict_weakening), but
again is an interface example, not a source-registered Plan or source-model
producer. Real new-boundary models must still supply these binder/center facts.
