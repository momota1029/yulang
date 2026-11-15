import Yulang.GeneralDictionaryDefaultAliasReadback215
import Yulang.GeneralDictionaryDefaultBinderCollisions214
import Yulang.GeneralDictionaryCurrentBranch215
import Yulang.GeneralDictionaryDefaultAliasProjection215

/-! Alias-class replay preserves the same journal and supplied raw-head model.
No equality of the numeric invocation names is required. -/
namespace Yulang.GeneralDictionaryAliasBranch215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same same_trans same_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralDictionaryDefaultBinderCollisions214 (point_fits point_binder nonpoint_name)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses uses_mem Compatible)
open GeneralDictionaryDefaultRevisit214 (BoundsFit frame_finished)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem historical_coherence (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (first last : Use) (one : first ∈ candidate.headSchema.variables) (two : last ∈ candidate.headSchema.variables)
    (oneActual : first.mode = .actual) (twoActual : last.mode = .actual)
    (oneInput : first.name ∉ candidate.packet.declaration.outputNames)
    (twoInput : last.name ∉ candidate.packet.declaration.outputNames)
    (model : Assignment) (valid : Models state model)
    (a b : Ty) (seenA : Observes model first.origin a) (seenB : Observes model last.origin b)
    (fitA : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name) a)
    (fitB : GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name) b)
    (same : candidate.binder first.name = candidate.binder last.name) : Equivalent a b := by
  by_cases pointA : ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs first.name).2
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).2
    · have left := point_fits candidate first.name oneInput pointA model a fitA
      have right := point_fits candidate last.name twoInput pointB model b fitB
      rw [same] at left
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · exact False.elim ((GeneralDictionaryDefaultConservative214.nonpoint_binder_endpoints_separate
        source bound path candidate frame.context_eq last.name twoInput pointB first.name).1
        (same.symm.trans (point_binder candidate first.name oneInput pointA)))
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs last.name).2
    · exact False.elim ((GeneralDictionaryDefaultConservative214.nonpoint_binder_endpoints_separate
        source bound path candidate frame.context_eq first.name oneInput pointA last.name).1
        (same.trans (point_binder candidate last.name twoInput pointB)))
    · have names := nonpoint_name candidate first.name last.name oneInput twoInput pointA pointB same
      have left := GeneralDictionaryDefaultAliasReadback215.candidate_actual checked source path historical candidate
        member frame.context_eq frame.center_recorded alias declaration first one oneActual valid
      have right := GeneralDictionaryDefaultAliasReadback215.candidate_actual checked source path historical candidate
        member frame.context_eq frame.center_recorded alias declaration last two twoActual valid
      rw [names] at left
      exact (same_trans left (same_symm right)).2.2 a b seenA seenB

theorem compatible_iff_bounds (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    Compatible candidate model ↔ BoundsFit candidate model := by
  constructor
  · exact fun compatible => compatible.2.2.1
  · intro bounds
    refine ⟨?_,?_,bounds,?_⟩
    · exact GeneralDictionaryDefaultAliasReadback215.candidate_tests checked source path historical candidate
        member frame.context_eq frame.center_recorded alias declaration model valid
    · intro index
      exact (GeneralDictionaryDefaultAliasReadback215.candidate_actual checked source path historical candidate
        member frame.context_eq frame.center_recorded alias declaration (uses candidate index) (uses_mem candidate index)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate index)) valid).1
    · intro i j first last same one two
      exact historical_coherence checked source bound path historical candidate
        member frame alias declaration (uses candidate i) (uses candidate j)
        (uses_mem candidate i) (uses_mem candidate j)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate j))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate j))
        model valid first last one two (bounds i first one) (bounds j last two) same

theorem revisit_branch (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) :
    ∃ extended, (Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended) ∧
      (∀ name ∈ GeneralDictionaryDefaultRawBranch214.support state candidate (uses candidate), extended name = model name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended := by
  apply (GeneralDictionaryDefaultRawBranch214.head_and_branch_extension_iff checked source bound path
    candidate frame (frame_finished frame) model valid branch).mpr
  apply (compatible_iff_bounds checked source bound path historical candidate member frame alias declaration model valid).mpr
  apply GeneralDictionaryDefaultProjectionBounds215.projection_bounds candidate frame model
  · apply GeneralDictionaryDefaultAliasProjection215.projection checked source path historical candidate member
      frame.context_eq frame.center_recorded _ alias declaration model valid
    rw [candidate.input_exact,frame.occurrence_eq]
    exact frame.located
  · exact GeneralDictionaryCurrentBranch215.branch_merges candidate model branch

end Yulang.GeneralDictionaryAliasBranch215
