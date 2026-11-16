import Yulang.GeneralDictionaryHeadSharingWitness220

namespace Yulang.GeneralDictionaryHeadSharingSpecification220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
open GeneralDictionaryHeadSharingConflict220 (Feasible)
open GeneralDictionaryDefaultKernel208 (Step)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Exact selected guard on inhabited reachable states, not on arbitrary states. -/
theorem selected_iff_feasible
    (reachable : B4TargetV8.Reachable (boundary roles) value root state)
    (inhabited : ∃ model, Models state model) :
    Local value state focus (.selected key children) ↔
      GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children) ∧
        Feasible (GeneralNominalCenteredHeadAllocEncoding.registry value) state focus key := by
  constructor
  · intro selected
    exact ⟨(GeneralDictionaryHeadSharingBoundary220.selected_iff.mp selected).1,
      GeneralDictionaryHeadSharingWitness220.selected_feasible reachable selected inhabited⟩
  · rintro ⟨old,feasible⟩
    exact GeneralDictionaryHeadSharingWitness220.selected_of_feasible old feasible

/-- Common head existence needs protected overlap in addition to head sharing. -/
theorem common_iff_sharing_overlap (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate) :
    (∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model) ↔
    ∃ model, Models state model ∧ GeneralDictionaryHeadSharing220.Holds candidate model ∧
      GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
        (GeneralDictionaryCurrentCompletion216.support state candidate) model := by
  rw [GeneralDictionaryCurrentHeadEquations217.common_iff checked source point ground coverage path candidate frame]
  constructor
  · rintro ⟨model,valid,agreement,overlap⟩
    exact ⟨model,valid,GeneralDictionaryHeadSharing220.holds_of_agreement
      candidate model (GeneralDictionaryDefaultRevisit214.frame_finished frame) agreement,overlap⟩
  · rintro ⟨model,valid,sharing,overlap⟩
    exact ⟨model,valid,GeneralDictionaryHeadSharing220.agreement_of_holds candidate model sharing,overlap⟩

end Yulang.GeneralDictionaryHeadSharingSpecification220
