import Yulang.GeneralDictionaryCurrentRoots215
import Yulang.GeneralDictionaryDefaultProjectionBounds215

/-! A current raw-head branch supplies its actual merge equations. Combined with
current centered projection readback this removes both formerly explicit model
premises; the supplied branch remains the same model as the journal. -/
namespace Yulang.GeneralDictionaryCurrentBranch215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles} {state : State roles}

theorem branch_merges (candidate : Plan roles) (model : Assignment)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings) := by
  have privateModel := branch.1
  unfold GeneralNominalRecursiveCandidates.privateState at privateModel
  exact ((GeneralNominalAllocation.propagate_models ..).mp
    ((GeneralNominalState.extend_models ..).mp privateModel).1).2.2

theorem revisit_branch (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) :
    ∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ GeneralDictionaryDefaultRawBranch214.support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended :=
  GeneralDictionaryDefaultProjectionBounds215.revisit_branch_of_projection checked source bound path historical
    candidate member frame identity declaration model valid branch
    (GeneralDictionaryCurrentRoots215.projection checked path historical candidate member frame identity declaration model valid)
    (branch_merges candidate model branch)
end Yulang.GeneralDictionaryCurrentBranch215
