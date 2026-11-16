import Yulang.GeneralDictionaryCurrentHeadEquations217

namespace Yulang.GeneralDictionaryHeadSharingSemanticSupport220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCountedProjection216 (Agreement)
open GeneralDictionaryCurrentCompletion216 (agreementSources agreement_iff origin_member)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Semantic dependency, not inclusion of an overapproximated source list. -/
def Depends (state : State roles) (pool : List Nat) : Prop :=
  ∀ first last : Assignment, (∀ name ∈ pool, first name = last name) →
    (Models state first ↔ Models state last)

theorem journal_depends (state : State roles) :
    Depends state (GeneralDictionaryDefault214ActualJournal.journalSources state) :=
  fun _ _ same => GeneralDictionaryDefault214ActualJournal.models_iff state same

theorem refresh_depends (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state context)
    (depends : Depends state pool) : Depends (refresh state context) pool := by
  intro first last same
  rw [GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate,
    GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate]
  exact depends first last same

theorem reobserve_depends
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state revision)
    (depends : Depends state pool) : Depends (change state revision.result) pool := by
  intro first last same
  rw [GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate,
    GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate]
  exact depends first last same

/-- Common raw head completion over any independently justified semantic pool. -/
theorem completion
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (depends : Depends state pool)
    (origins : agreementSources candidate ⊆ pool)
    (endpoints : GeneralNominalAllocationSupport.Endpoints candidate.packet.bindings pool)
    (previous : Assignment) (valid : Models state previous) (sharing : Agreement candidate previous)
    (overlap : GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings pool previous) :
    ∃ extended, Models state extended ∧ Agreement candidate extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      (∀ name ∈ pool, extended name = previous name) := by
  let extended := GeneralDictionaryMixedMerge216.patch candidate.packet.context.state candidate.packet.registry
    candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings pool previous
  have kept : ∀ name ∈ pool, extended name = previous name := GeneralDictionaryMixedMerge216.preserves _ _ _ _ _ pool previous
  have journal : Models state extended := (depends previous extended (fun name member => (kept name member).symm)).mp valid
  have shared : Agreement candidate extended := (agreement_iff candidate previous extended
    (fun name member => (kept name (origins member)).symm)).mp sharing
  exact ⟨extended,journal,shared,
    (GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path candidate frame
      extended journal shared).mpr (GeneralDictionaryMixedMerge216.merges_valid overlap endpoints),kept⟩

/-- The final exact-head extension retains the same independent overlap obligation. -/
theorem common_head (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (depends : Depends state pool)
    (origins : agreementSources candidate ⊆ pool)
    (endpoints : GeneralNominalAllocationSupport.Endpoints candidate.packet.bindings pool)
    (previous : Assignment) (valid : Models state previous) (sharing : Agreement candidate previous)
    (overlap : GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings pool previous) :
    ∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended := by
  obtain ⟨merged,journal,shared,branch,_⟩ := completion source point ground coverage path candidate frame
    depends origins endpoints previous valid sharing overlap
  obtain ⟨extended,both,_,head⟩ := GeneralDictionaryCurrentHeadEquations217.branch_extension
    checked source point ground coverage path candidate frame merged journal shared branch
  exact ⟨extended,both.1,both.2,head⟩

/-- Exact support-preserving criterion for a semantic dependency pool. -/
theorem extension_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (depends : Depends state pool)
    (origins : agreementSources candidate ⊆ pool)
    (endpoints : GeneralNominalAllocationSupport.Endpoints candidate.packet.bindings pool)
    (previous : Assignment) (valid : Models state previous) (sharing : Agreement candidate previous)
 :
    (∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      (∀ name ∈ pool, extended name = previous name)) ↔
    GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings pool previous := by
  constructor
  · rintro ⟨extended,_,branch,kept⟩
    exact GeneralDictionaryMergeCriterion216.necessary _ _ _ _ _ pool endpoints previous extended kept
      (GeneralDictionaryCurrentBranch215.branch_merges candidate extended branch)
  · intro overlap
    obtain ⟨extended,journal,_,branch,kept⟩ := completion source point ground coverage path candidate frame
      depends origins endpoints previous valid sharing overlap
    exact ⟨extended,journal,branch,kept⟩

end Yulang.GeneralDictionaryHeadSharingSemanticSupport220
