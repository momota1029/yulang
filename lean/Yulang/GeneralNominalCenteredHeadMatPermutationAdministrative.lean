import Yulang.GeneralNominalCenteredHeadMatPermutationLocal

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatPermutationAdministrative
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalJournalPermutation (ContextPair)
variable {roles : Roles.RoleDecls} {relation : Plan roles → Plan roles → Prop} {first last : State roles}

theorem recorded (same : GeneralNominalMetadataEquivalence.Same one two) (observation) :
    GeneralCanonicalObservations.Recorded one observation ↔ GeneralCanonicalObservations.Recorded two observation := by
  obtain ⟨_,_,rfl,_,_⟩ := same
  constructor <;> intro recorded <;> cases recorded with
  | scalar _ _ seen => exact .scalar _ _ seen
  | structural _ _ _ seen => exact .structural _ _ _ seen
  | nominal _ _ seen => exact .nominal _ _ seen

theorem cache_snapshot (same : GeneralNominalMetadataEquivalence.Same one two) (state : State roles) :
    GeneralNominalCenteredHeadMatStepObservations.CacheSound state one ↔
      GeneralNominalCenteredHeadMatStepObservations.CacheSound state two := by
  simp only [GeneralNominalCenteredHeadMatStepObservations.CacheSound,recorded same]

noncomputable def refresh_certificate (same : Related relation first last)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh first context) :
    GeneralNominalCenteredHeadMatStepRefresh.Refresh last context where
  refines := GeneralNominalMetadataEquivalence.refines_left same.core.current.context.state certificate.refines
  interpretation := certificate.interpretation.trans same.core.current.context.interpretation
  support := fun source member => (GeneralNominalMetadataEquivalence.sources same.core.current.context.state source).mp
    (certificate.support source member)
  constraints := fun model valid => certificate.constraints model ((same.models model).mpr valid)
  cache := (same.cache context.state).mp certificate.cache

theorem change_related (same : Related relation first last) (raw : Raw one two)
    (onePackets : one.packets = first.core.erased.current.packets)
    (twoPackets : two.packets = last.core.erased.current.packets) :
    Related relation (change first one) (change last two) :=
  ⟨⟨raw,same.core.source,same.core.centers,same.core.roots⟩,same.coherent,same.recorded,same.plans,same.effects,
    fun plan member => onePackets.symm ▸ same.packetsLeft plan member,
    fun plan member => twoPackets.symm ▸ same.packetsRight plan member⟩

theorem refresh_related (same : Related relation first last) (context) :
    Related relation (refresh first context) (refresh last context) :=
  change_related same (same.core.current.regenerate (ContextPair.refl context)) rfl rfl

theorem raw_revision {first last : GeneralNominalSaturationState.State roles} (same : Raw first last)
    (revision : GeneralNominalReobservationSteps.Revision first) :
    ∃ other : GeneralNominalReobservationSteps.Revision last,
      GeneralNominalMetadataEquivalence.Same revision.snapshot other.snapshot ∧
      (GeneralNominalReobservationSteps.Improves revision ↔ GeneralNominalReobservationSteps.Improves other) := by
  rcases first with ⟨one,packets,sites,edges,aliases⟩
  rcases last with ⟨two,otherPackets,otherSites,otherEdges,otherAliases⟩
  obtain ⟨allocated,reserved,contextEq,keys,names⟩ := same.context.replace_form
  dsimp at contextEq
  subst two
  let other : GeneralNominalReobservationSteps.Revision
      ⟨⟨GeneralNominalMetadataEquivalence.replace one.state allocated reserved,one.interpretation⟩,
        otherPackets,otherSites,otherEdges,otherAliases⟩ :=
    ⟨revision.entries,revision.catalogue,revision.opaqueHeads,revision.domain⟩
  exact ⟨other,⟨allocated,reserved,rfl,keys,names⟩,Iff.rfl⟩

theorem reobserve (same : Related relation first last)
    (revision : GeneralNominalReobservationSteps.Revision first.core.erased.current)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve first revision) :
    ∃ other : GeneralNominalReobservationSteps.Revision last.core.erased.current,
      GeneralNominalCenteredHeadMatStepRefresh.Reobserve last other ∧
      (GeneralNominalReobservationSteps.Improves revision ↔ GeneralNominalReobservationSteps.Improves other) ∧
      Related relation (change first revision.result) (change last other.result) := by
  obtain ⟨other,snapshots,improves⟩ := raw_revision same.core.current revision
  have contexts : ContextPair revision.result.context other.result.context :=
    ⟨snapshots,same.core.current.context.interpretation⟩
  refine ⟨other,⟨?_,?_⟩,improves,change_related same (same.core.current.regenerate contexts) rfl rfl⟩
  · intro model valid
    exact (GeneralNominalMetadataEquivalence.models same.core.current.context.state model).mp
      (certificate.raw model ((GeneralNominalMetadataEquivalence.models snapshots model).mpr valid))
  · exact (cache_snapshot snapshots last).mp ((same.cache revision.snapshot).mp certificate.cache)

theorem administrative (same : Related relation first last) (action : Administrative first focus next) :
    ∃ other, Administrative last focus other ∧ Related relation next other := by
  cases action with
  | enqueue linked absent =>
      exact ⟨_,.enqueue focus ((GeneralNominalMetadataEquivalence.linked same.core.current.context.state _).mp linked)
        (fun site member => absent site ((same.core.current.sites site).mpr member)),
        change_related same (same.core.current.enqueue focus) rfl rfl⟩
  | refresh context certificate source member unknown known =>
      exact ⟨_,.refresh focus context (refresh_certificate same certificate) source
        ((GeneralNominalMetadataEquivalence.sources same.core.current.context.state source).mp member)
        (fun present => unknown ((GeneralNominalMetadataEquivalence.known same.core.current.context.state source).mpr present)) known,
        refresh_related same context⟩
  | equate one two memberOne memberTwo equal novel =>
      refine ⟨_,.equate focus one two
        ((GeneralNominalMetadataEquivalence.sources same.core.current.context.state one).mp memberOne)
        ((GeneralNominalMetadataEquivalence.sources same.core.current.context.state two).mp memberTwo)
        (fun model valid => equal model ((same.models model).mpr valid)) ?_,
        change_related same (same.core.current.equate one two) rfl rfl⟩
      exact fun valid => novel (fun model models => valid model
        ((GeneralNominalMetadataEquivalence.models same.core.current.context.state model).mp models))
  | reobserve revision certificate improved =>
      obtain ⟨other,certificate,improves,paired⟩ := reobserve same revision certificate
      exact ⟨_,.reobserve focus other certificate (improves.mp improved),paired⟩

theorem merging (same : Related relation first last) (one two : Site roles) :
    Related relation (merge first one two) (merge last one two) :=
  change_related same (same.core.current.merge one.observed two.observed) rfl rfl

end Yulang.GeneralNominalCenteredHeadMatPermutationAdministrative
