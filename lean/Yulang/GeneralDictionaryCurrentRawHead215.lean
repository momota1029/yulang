import Yulang.GeneralDictionaryDefaultAliasProjection215
import Yulang.GeneralDictionaryDefaultAliasRawProjection215
import Yulang.GeneralDictionaryCurrentPropagation215
import Yulang.GeneralDictionaryCurrentBranch215
import Yulang.GeneralDictionaryDefaultAliasConflicts215
import Yulang.GeneralNominalMergeResidual178

/-! In a fixed journal model, historical alias reinspection leaves exactly
current merge-slot equations. This is not an existential amalgamation theorem. -/
namespace Yulang.GeneralDictionaryCurrentRawHead215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem head_iff_merges (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings) := by
  constructor
  · exact GeneralDictionaryCurrentBranch215.branch_merges candidate model
  · intro merges
    have projection := GeneralDictionaryDefaultAliasProjection215.projection checked source path historical candidate
      registered current inputRegistered located alias declaration model valid
    refine ⟨?_,GeneralDictionaryDefaultAliasRawProjection215.projection checked source path historical candidate
      registered current inputRegistered located alias declaration model valid⟩
    unfold GeneralNominalRecursiveCandidates.privateState
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨?_,?_⟩
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨?_,GeneralDictionaryCurrentPropagation215.capture_compatible candidate model projection,merges⟩
      rw [current]
      exact valid.1
    · exact GeneralDictionaryCurrentPropagation215.raw_checks candidate inputRegistered located model valid projection

theorem not_failed_of_merges (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings)) :
    ¬ GeneralNominalCenteredHeadCandidates.Failed candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration := by
  intro failed
  obtain ⟨_,_,bounds,found,_,_,failure⟩ := failed
  have foundCurrent := located
  rw [candidate.input_exact] at foundCurrent
  have equal : bounds = candidate.packet.bounds := Option.some.inj (found.symm.trans foundCurrent)
  subst bounds
  rcases failure with conflicts | impossible
  · exact conflicts (GeneralDictionaryDefaultAliasConflicts215.conflicts_empty checked source path historical candidate
      registered current inputRegistered located alias declaration model valid)
  · exact impossible ⟨model,(head_iff_merges checked source path historical candidate registered
      current inputRegistered located alias declaration model valid).mpr merges⟩

theorem head_iff_capture_extrema (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ↔
    GeneralNominalMergeResidual178.CaptureExtrema candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings model := by
  rw [head_iff_merges checked source path historical candidate registered current inputRegistered
    located alias declaration model valid,GeneralNominalMergeResidual178.merges_iff_extrema]

end Yulang.GeneralDictionaryCurrentRawHead215
