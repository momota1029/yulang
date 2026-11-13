import Yulang.GeneralDictionarySemanticCollapseBranch
import Yulang.GeneralDictionaryLinearLeaf

/-! Completion guards across depth-two capture collapse. These are syntactic
transport facts, not assertions that a historical branch holds in all models. -/
namespace Yulang.GeneralDictionaryCollapseReadiness
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralDeclarations
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

theorem arguments_same (root : GeneralSourceDictionaries.Occurrence roles) :
    arguments (currentContext revision) root = arguments state.context root := rfl

theorem metadata_same (registry : Registry) :
    Metadata registry (currentContext revision) ↔ Metadata registry state.context := Iff.rfl

theorem finished (s : Shape revision) (declaration : Declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s]) :
    Finished (report state.context declaration [(s.root,s.root)]) ∧
    Finished (report (currentContext revision) declaration [(s.root,s.root)]) := by
  rw [(reports s declaration queries).1,(reports s declaration queries).2]
  exact ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩

theorem generated_same (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) :
    generated registry (currentContext revision) root declaration checked [(s.root,s.root)] =
    generated registry state.context root declaration checked [(s.root,s.root)] := by
  unfold generated
  rw [terminal_requests _ _ _ _ _ _ terminal,terminal_requests _ _ _ _ _ _ terminal]
  rfl

theorem ready_same (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) :
    RequestReady registry (currentContext revision) root declaration checked [(s.root,s.root)] ↔
    RequestReady registry state.context root declaration checked [(s.root,s.root)] := by
  unfold RequestReady
  rw [generated_same s registry root declaration checked terminal]

end Yulang.GeneralDictionaryCollapseReadiness
