import Yulang.GeneralRebaseRefreshRank275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseRefreshClosure275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryVersionedSecondEquality233 (supported index_model)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralRebaseRefreshRank275 (Anchor Hop Path snapshot)
open GeneralNominalReobservationSteps (PointDescriptor PointClosed PointParameter)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known sources)
open CommonNominalFullCarrier
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalVersionedMixedObservations233 (Refresh)

theorem width_not_nominal {name : Nat} {args : List Argument} :
 ¬ Equivalent .emptyRecord (nominal name args) := by
 intro same
 have impossible := tag_subtype (tagged_shape (.record []) [] rfl) (tagged_nominal name args) same.1
 cases impossible

theorem only_original_nominals {state : State roles} (anchor : Anchor state)
 (slot : Fin (snapshot state).base.slots) (descriptor : GeneralNominalState.Descriptor (snapshot state).base.slots)
 (seen : (snapshot state).nominals slot = some descriptor) :
 (snapshot state).base.source slot = 0 ∨ (snapshot state).base.source slot = 1 := by
 have listed : (snapshot state).base.source slot ∈ sources (snapshot state) :=
   GeneralNominalAllocationSupport.slot_source _ slot
 obtain ⟨index,equal⟩ := supported (anchor.support _ listed)
 have valid := (anchor.models extended).mpr installed_model
 obtain ⟨args,_,held⟩ := valid.1.1.2.1 slot descriptor seen
 rw [← equal,index_model] at held
 cases index
 · exact Or.inl equal.symm
 · exact Or.inr equal.symm
 · exact False.elim (width_not_nominal held)
 · exact False.elim (GeneralDictionaryGroundCopy218Refresh.top_no_head
     (.nominal descriptor.declaration.name args.length) ⟨args,rfl,held⟩)
 · exact False.elim (GeneralDictionaryOptionalOutput229.no_test
     (.nominal descriptor.declaration.name args.length) ⟨args,rfl,held⟩)
 · exact False.elim (GeneralDictionaryOptionalOutput229.no_test
     (.nominal descriptor.declaration.name args.length) ⟨args,rfl,held⟩)
 · exact False.elim (width_not_nominal held)
 · exact False.elim (width_not_nominal held)
 · exact False.elim (width_not_nominal held)

theorem rename_point {n m : Nat} (embed : Fin n → Fin m)
 (descriptor : GeneralNominalState.Descriptor n) (isPoint : PointDescriptor descriptor) :
 PointDescriptor (GeneralNominalRefinements.renameDescriptor embed descriptor) := by
 intro parameter existsAt
 change parameter ∈ descriptor.arguments.map (GeneralNominalRefinements.renameParameter embed) at existsAt
 obtain ⟨old,found,rfl⟩ := List.mem_map.mp existsAt
 have synchronized := isPoint old found
 cases old with
 | type pair =>
   change pair.1 = pair.2 at synchronized
   exact congrArg embed synchronized
 | row pair =>
   change pair.1 = pair.2 at synchronized
   exact congrArg embed synchronized

structure Gates (state : State roles) : Prop where
 anchor : Anchor state
 nominal_zero : ∃ slot, (snapshot state).base.source slot = 0 ∧ ∃ d, (snapshot state).nominals slot = some d
 nominal_one : ∃ slot, (snapshot state).base.source slot = 1 ∧ ∃ d, (snapshot state).nominals slot = some d
 points : PointClosed (snapshot state)
 equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed state
 sites : state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]
 centers : state.core.sites = [GeneralNominalCenters.rootSite GeneralDictionaryJournalRefinement228Source.snapshot.seed root]
 edges : state.core.erased.current.edges = []

theorem gates_initial : Gates installed :=
 ⟨GeneralRebaseRefreshRank275.anchor_start,
   ⟨(0 : Fin 5),rfl,_,rfl⟩,⟨(1 : Fin 5),rfl,_,rfl⟩,
   GeneralDictionaryVersionedSecondStable233.point_closed,
   GeneralDictionaryVersionedSecondEquality233.equality_closed,
   GeneralDictionaryVersionedSecondSelected233.raw_sites,GeneralDictionaryVersionedSecondSelected233.centers,
   GeneralDictionaryVersionedSecondStable233.edges_empty⟩

theorem nominal_retained {state : State roles} {ctx : GeneralNominalCandidates.Context}
 (cert : Refresh state ctx) {uid : Nat}
 (old : ∃ slot, (snapshot state).base.source slot = uid ∧ ∃ d, (snapshot state).nominals slot = some d) :
 ∃ slot, ctx.state.base.source slot = uid ∧ ∃ d, ctx.state.nominals slot = some d := by
 obtain ⟨slot,same,d,seen⟩ := old
 exact ⟨cert.refines.base.embed slot,(cert.refines.base.source slot).trans same,
   _,cert.refines.nominals slot d seen⟩

theorem gates_next {state : State roles} (prior : Gates state) (ctx : GeneralNominalCandidates.Context)
 (cert : Refresh state ctx) :
 Gates (GeneralNominalVersionedRefresh232.refresh state ctx) := by
 have anchor := GeneralRebaseRefreshRank275.anchor_next prior.anchor ctx cert
 refine ⟨anchor,nominal_retained cert prior.nominal_zero,nominal_retained cert prior.nominal_one,
   ?_,GeneralNominalVersionedMixedRefreshEquality234.equality_closed cert prior.equality_closed,
   prior.sites,prior.centers,prior.edges⟩
 intro slot descriptor seen
 change Fin ctx.state.base.slots at slot
 change GeneralNominalState.Descriptor ctx.state.base.slots at descriptor
 change ctx.state.nominals slot = some descriptor at seen
 have source := only_original_nominals anchor slot descriptor seen
 change ctx.state.base.source slot = 0 ∨ ctx.state.base.source slot = 1 at source
 have contains : ∃ prev, (snapshot state).base.source prev = ctx.state.base.source slot ∧
     ∃ d, (snapshot state).nominals prev = some d := by
   rcases source with zero|one
   · rw [zero]; exact prior.nominal_zero
   · rw [one]; exact prior.nominal_one
 obtain ⟨prev,same,d,recorded⟩ := contains
 have equal : cert.refines.base.embed prev = slot :=
   ctx.state.base.source_injective ((cert.refines.base.source prev).trans same)
 have sameDescriptor := cert.refines.nominals prev d recorded
 rw [equal,seen] at sameDescriptor
 cases Option.some.inj sameDescriptor
 exact rename_point _ d (prior.points prev d recorded)

theorem gates_hop {state next : State roles} (good : Gates state) (hop : Hop state next) : Gates next := by
 cases hop with
 | step ctx cert _ _ _ _ => exact gates_next good ctx cert

theorem gates_path {finish : State roles} {n : Nat} (path : Path installed finish n) : Gates finish := by
 have start := gates_initial
 induction path with
 | empty => exact start
 | more _ hop ih => exact gates_hop ih hop

def NovelInstall (s t : State roles) : Prop :=
 ∃ effect : Effect roles, Installable registry s effect ∧ effect.plan.packet.site.occurrence = root ∧
   ¬ Committed s effect.plan ∧ t = GeneralNominalVersionedInstall232.install s effect

theorem step_partition {s t : State roles} (good : Gates s) (action : Step registry root s t) :
 Hop s t ∨ NovelInstall s t := by
 obtain ⟨focus,generated,atStep⟩ := action
 have focusRoot := GeneralNominalVersionedMixedTerminalStable234.generated_only good.sites good.edges generated
 cases atStep with
 | administrative a =>
   cases a with
   | enqueue _ absent => exact False.elim (absent _ (good.sites ▸ List.mem_singleton_self _) focusRoot.symm)
   | refresh c cert id tracked unknown known => exact Or.inl (.step c cert id tracked unknown known)
   | equate first last one two equal novel => exact False.elim (novel (good.equality_closed first last one two equal))
   | reobserve revision _ improves =>
     exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision good.points revision improves)
 | refresh _ c cert id tracked unknown known => exact Or.inl (.step c cert id tracked unknown known)
 | install effect available novel => exact Or.inr ⟨effect,available,focusRoot,novel,rfl⟩
 | merge first last one two _ novel =>
   rw [good.centers] at one two
   cases List.mem_singleton.mp one
   cases List.mem_singleton.mp two
   exact False.elim (novel (.refl _))

end Yulang.GeneralRebaseRefreshClosure275
