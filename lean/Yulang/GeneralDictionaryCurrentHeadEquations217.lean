import Yulang.GeneralDictionaryCurrentAgreement217
import Yulang.GeneralDictionaryCurrentCompletion216

namespace Yulang.GeneralDictionaryCurrentHeadEquations217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCountedProjection216 (Agreement)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses)
open GeneralDictionaryDefaultRevisit214 (BoundsFit)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem extension_iff (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ GeneralDictionaryDefaultConservative214.support state candidate (uses candidate), extended name = previous name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended) ↔
        Agreement candidate previous ∧ BoundsFit candidate previous := by
  rw [GeneralDictionaryDefaultHeadEquationExtension214.head_equations_extension_iff checked source
    (GeneralDictionaryDefaultAncestry208.ground_depth_bound source point ground coverage) path candidate frame
    (GeneralDictionaryDefaultRevisit214.frame_finished frame) previous valid]
  exact GeneralDictionaryCurrentAgreement217.compatible_iff source point ground coverage path candidate frame previous valid

theorem branch_extension (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) :
    ∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ GeneralDictionaryDefaultRawBranch214.support state candidate (uses candidate), extended name = model name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended := by
  have projection := (GeneralDictionaryCountedProjection216.projection_iff source point ground coverage path candidate frame model valid).mpr agreement
  have merges := GeneralDictionaryCurrentBranch215.branch_merges candidate model branch
  have fits := GeneralDictionaryDefaultProjectionBounds215.projection_bounds candidate frame model projection merges
  exact (GeneralDictionaryDefaultRawBranch214.head_and_branch_extension_iff checked source
    (GeneralDictionaryDefaultAncestry208.ground_depth_bound source point ground coverage) path candidate frame
    (GeneralDictionaryDefaultRevisit214.frame_finished frame) model valid branch).mpr
      (GeneralDictionaryCurrentAgreement217.compatible source point ground coverage path candidate frame model valid agreement fits)

theorem common_head (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model)
    (overlap : GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
      (GeneralDictionaryCurrentCompletion216.support state candidate) model) :
    ∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended := by
  obtain ⟨merged,journal,sharing,branch⟩ :=
    (GeneralDictionaryCurrentCompletion216.common_iff source point ground coverage path candidate frame).mpr
      ⟨model,valid,agreement,overlap⟩
  obtain ⟨extended,valid,_,head⟩ := branch_extension checked source point ground coverage path candidate frame
    merged journal sharing branch
  exact ⟨extended,valid.1,valid.2,head⟩

theorem common_iff (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate) :
    (∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model) ↔
    ∃ model, Models state model ∧ Agreement candidate model ∧
      GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
        (GeneralDictionaryCurrentCompletion216.support state candidate) model := by
  constructor
  · rintro ⟨model,valid,branch,head⟩
    have agree := ((extension_iff checked source point ground coverage path candidate frame model valid).mp
      ⟨model,valid,fun _ _ => rfl,head⟩).1
    exact (GeneralDictionaryCurrentCompletion216.common_iff source point ground coverage path candidate frame).mp
      ⟨model,valid,agree,branch⟩
  · rintro ⟨model,valid,agreement,overlap⟩
    exact common_head checked source point ground coverage path candidate frame model valid agreement overlap

end Yulang.GeneralDictionaryCurrentHeadEquations217
