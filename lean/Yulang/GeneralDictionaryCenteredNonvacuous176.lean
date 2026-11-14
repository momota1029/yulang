import Yulang.GeneralDictionaryCenteredRevision176
import Yulang.GeneralDictionaryCenteredInhabited176

/-! A nonvacuous whole-dictionary consumer for an explicitly certified history.
The same state transitions satisfy both local-observation transport and the
syntactic aligned-output merge condition. Neither unrestricted execution nor
existence of a finite recorded dictionary is asserted. -/
namespace Yulang.GeneralDictionaryCenteredNonvacuous176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence
open GeneralDictionarySharedRecordedTree (RecordedTree)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  GeneralDictionaryCenteredRevision176.Step registry root before after ∧
  GeneralDictionaryCenteredInhabited176.AlignedStep registry root before after

theorem revision_trace (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralDictionaryCenteredRevision176.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih step.1

theorem aligned_trace (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralDictionaryCenteredInhabited176.AlignedStep registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih step.2

theorem actual_trace (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalCenteredSteps.Step registry root) before after :=
  GeneralDictionaryCenteredInhabited176.trace_actual (aligned_trace path)

theorem initial_dictionary_nonvacuous (context : GeneralNominalCandidates.Context)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (sourceModel : Assignment) (sourceValid : GeneralNominalState.Models context.state sourceModel)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (payload : Payload) (tree : RecordedTree state.erased.current root payload) :
    GeneralNominalSupport.Discharged state.erased.current root ∧
      (∃ model, Models state model ∧ Evidence registry state.erased.current.context model root payload) ∧
      ∀ model, Models state model → Evidence registry state.erased.current.context model root payload := by
  have evidence := GeneralDictionaryCenteredRevision176.initial_trace_evidence context (revision_trace path) tree
  have inhabited := GeneralDictionaryCenteredInhabited176.trace_inhabited (aligned_trace path)
    ⟨sourceModel,(point_initial_models context root point sourceModel).mpr sourceValid⟩
  obtain ⟨model,valid⟩ := inhabited
  exact ⟨GeneralDictionarySharedRecordedTree.discharged tree,⟨model,valid,evidence model valid⟩,evidence⟩

end Yulang.GeneralDictionaryCenteredNonvacuous176
