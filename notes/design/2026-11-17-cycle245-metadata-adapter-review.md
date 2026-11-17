# Cycle 245: metadata transport adapter review

Read-only source review. Paths below are relative to `lean/Yulang/`. This note
adds no Lean declaration and does not claim all boundary or cache coverage.
The proposed adapter steps are not proved by listing these fields.

## 1. The boundary is a predicate interface, not a term container

`B4TargetV8.SourceBoundary` (`B4TargetV8.lean`) extends V7 with
`SharingConflict : v.Registry -> v.State -> v.Demand -> Prop`. V7 adds
`MergedOutputConflict`; V6 adds `OutputConflict`; V5 adds `Initial`.
The actual adapter `GeneralNominalPointSourceBoundary240.boundary`
(`GeneralNominalPointSourceBoundary240.lean`) supplies/overrides `CandidateK2`,
`InspectionPending`, `Survivor`, `Step`, `Stable`, `Evidence`, `OutputConflict`
and `SharingConflict` using the encoded source registry.

These predicates are not `CompTerm` fields. Query transport alone gives no
transport of reachability, classification, candidate uniqueness, installation,
Evidence, or scheduler transitions. An adapter must establish a state relation
and a theorem for each predicate it actually needs. In particular, the new
owner-table State is not definitionally the boundary's journal State.

## 2. Actual current, source, and history storage

`GeneralNominalVersionedJournal232.State` (`GeneralNominalVersionedJournal232.lean`):

- `legacy : Legacy.State roles`;
- `plans : List (Plan roles)`;
- `effects : List (Effect roles)`;
- `State.core` is an abbreviation for `state.legacy.core`.

`GeneralNominalVersionedJournal232.Effect` has `registry`, `snapshot`, `plan`,
and dependent proof fields `frame`, `unique`, `ready`. `Effect.Holds` uses the
historical `snapshot`; `Effect.Live` uses a supplied current `core`. Thus
rewriting the live copy alone would omit historical constraints. Updating a
snapshot or plan is not a record map on query payloads: the three proof fields
must be reconstructed with their changed indices.

`GeneralNominalCenteredSteps.State` (`GeneralNominalCenteredSteps.lean`) has
`erased`, `sites`, `plans`, `sourceSites`, `sourceRecorded`.
`erased : GeneralNominalSupport.Tracked roles` has `source`, `current`, `facts`
(`GeneralNominalSupport.lean`). Its `source` is a Context; `current` is the
saturation State. `GeneralNominalSaturationState.State`
(`GeneralNominalSaturationState.lean`) has `context`, `packets`, `sites`, `edges`,
`aliases`. Edges and aliases are structural identity data, not term evaluations.

Raw `GeneralNominalState.State` (`GeneralNominalState.lean`) has `base`, `view`,
`constructors`, `nominals`, `catalogue`, `bodies_opaque`, `seed`, `allocated`,
`reserved`, `ordinary`. Only `ordinary` already has type `List (Atom Nat)`.
The finite-slot `base` supplies separate `source` and `rowSource` maps. A raw
state is therefore not just the new owner table's base atoms plus definitions.

## 3. Existing expression views provide real candidate attachment points

The prior modules already convert several actual payloads to expression views.
They are more precise starting points than inventing a flattened metadata type.

### Raw view (`GeneralNominalRebaseRawView243.lean`)

`View` fields:

- `slots : Nat`, `slot : Fin slots -> CompTerm Nat`;
- `ordinary : List Atom`;
- `heads : Fin slots -> Option (TyTerm Nat)`;
- `intervals : List (Fin slots × Fin slots)`;
- `nominals : Fin slots -> Option Descriptor`.

`Descriptor` has `name` and `arguments : List Parameter`; `Parameter` is either
`type lower upper : TyTerm Nat` or `row lower upper : RowTerm Nat`.
`slot state mapping index` deliberately combines the type projection of
`mapping (state.source index)` with the row projection of
`mapping (state.rowSource index)`. One must not replace these two names by a
single assumed slot identity.

The slot payloads directly fit `querySubst`; type/row endpoints can use its
corresponding projection. Ordinary atoms fit the atom substitution laws.
`View.Models`, however, also quantifies nominal witnesses through
`Descriptor.Denotes` and `FitsAll`; it is not merely a conjunction of query
values. A view-level congruence/transport lemma must still preserve those
witnesses and finite-slot indexing. Keeping `intervals` as index pairs is valid
only while the slot carrier and indexing remain unchanged.

### Origin and inspection views

`GeneralNominalRebaseOriginView243.Origin`
(`GeneralNominalRebaseOriginView243.lean`) has constructors:
`source (term : TyTerm Nat)`, `nominal parent name index`, and
`structural parent shape index`. Existing `compile`, `subst`, `compile_exact`
and `subst_exact` transport expressions and the relational `Observes` under
exact readback. They preserve the structural path data.

Important distinction: cycle245 query_forward gives mutual subtyping, not
literal type-value equality. The `Observes.source` constructor returns exactly
the evaluated source term. If that value changes to an equivalent but different
syntax representative, `Observes ... origin actual` for the *same literal*
`actual` need not remain true at a source origin. A new theorem should transport
observed witnesses up to `Equivalent`, then show predicates such as Fits and
Test.Holds are invariant. It must not substitute query Probe iff for this
relational theorem. Existing exact-readback `subst_exact` alone does not close
the later comparison to the original assignment.

`GeneralNominalRebaseProjectionView243.Bounds` has `lower`, `upper : TyTerm Nat`.
`Capture` has `name`, `bounds`, `origin : Option Origin`. `Report` has `anchors`,
`tests`, `captures`. Its `Report.Models` includes existence of observed values,
all observed values fitting bounds, test validity, cross-capture fits and
cross-capture equivalence. Each needs the origin-witness transport above.

The actual `GeneralNominalRecursiveInspection.Report state`
(`GeneralNominalRecursiveInspection.lean`) additionally has `inspected`,
`checked`, `blocked`, `conflicts`, `arity`, besides `captures`, `anchors`,
`tests`. The expression projection Report does not store all those control
lists. Transport of its semantic Models is not preservation of inspector
Finished status or the actual discovery computation.

`GeneralNominalRebaseObservedSite243.Argument`
(`GeneralNominalRebaseObservedSite243.lean`) has `bounds` and `origin`.
`compileArgument` reads the actual site's demand interval pair and optional
input origin. It has the same bounds/origin obligations, not just a CompTerm
bundle operation.

### Live, packet and journal views

`GeneralNominalRebaseLiveView243.Argument` has type-term `lower`, `upper`,
`center`; `Output` has `name`, `target : TyTerm Nat`; `Site` has `identity`,
`role`, `arguments`, `outputs` (`GeneralNominalRebaseLiveView243.lean`). Existing
`Argument.subst` and `Site.subst` are useful attachment points. `Site.Holds`
only constrains arguments, not outputs; output payload transport therefore
needs its own query/equation statement rather than inference from Site.Holds.

`GeneralNominalRebasePacketView243.Packet`
(`GeneralNominalRebasePacketView243.lean`) has `raw`, `ordinary`, `projection`,
`input`, `binders`, `head`, `children`, `outputs`. `Child` has `site` and
`equations`. A packet adapter needs all these nested components, including the
schema/equation views, not merely its `input` site's term list.

`GeneralNominalRebaseJournalView243.Journal`
(`GeneralNominalRebaseJournalView243.lean`) has `current`, `source`, `observed`,
`sites`, `packets`, `effects`. Its view `Effect` has `raw`, `projection`,
`historical`, `live`. `compile_exact` assumes `LegacyEmpty`; `source_exact` and
`point_source_exact` obtain that assumption from the respective actual source
reachability. Do not invoke an unconditional whole-journal equivalence or
silently discard legacy plans/effects. Compilation is noncomputable, including
prior alias-class request enumeration; this does not establish an executable
finite metadata updater.

## 4. Cache is a proof-bearing observation interface, not the query bundle

`GeneralCanonicalObservations.Observation`
(`GeneralCanonicalObservations.lean`) has constructors:

- `normalized (base : GeneralSourceState.State) (slot : Fin base.slots)
  (term : TyTerm (Fin base.slots))`;
- `nominal (base : GeneralSourceState.State) (slot : Fin base.slots)
  (descriptor : GeneralNominalState.Descriptor base.slots)`.

`Recorded snapshot observation` is generated by certified scalar/structural
heads or a matching nominal descriptor. `Cache state` has
`contains : Observation -> Prop` and
`justified : ∀ observation, contains observation -> canonical state observation`.
Its contents need not be an enumerated list. Source/support data comes from the
observation's whole finite base. Normalized terms require the actual slot
substitution into Nat-name expressions before the new query law can apply.
Nominal observations require descriptor witness transport as above.

`GeneralNominalVersionedMixedObservations233.CacheSound state snapshot`
(`GeneralNominalVersionedMixedObservations233.lean`) says every `Recorded`
observation is `Justified`, using separately trusted old and new fact slices.
`Refresh state context` has `refines`, `interpretation`, `support`, `constraints`,
`cache`; `Reobserve state revision` has `raw`, `cache`. Query equality does not
supply Refines, unchanged interpretation, source-support inclusion, trusted
facts, or newly indexed Recorded certificates. The module itself describes an
auxiliary interface not installed in Kernel232; particular later kernels must
be checked rather than inferred from the type's existence.

## 5. Concrete next steps and nonclaims

A small sound next adapter would first prove value-equivalence transport for
RawView interval/head/parameter predicates, and a separate observed-witness
transport theorem for OriginView. Then extend to ProjectionView and the nested
journal views under their existing exactness hypotheses. Keep finite tags,
slot indices, identity data and history/live copies explicit throughout.

This review does not enumerate every SourceBoundary predicate or every cache
consumer, prove actual state mutation, or build a SourceBoundary simulation.
The new CompTerm transport is a semantic ingredient for these adapters, not an
all-metadata-coverage certificate, an inspector-completeness result, or a
termination result.
