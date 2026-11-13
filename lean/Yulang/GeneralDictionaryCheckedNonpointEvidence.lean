import Yulang.GeneralDictionaryNonpointEvidence
import Yulang.GeneralDictionaryActualSchemaScope

/-! Checked declarations discharge the generated variable-name scope. Remaining
restrictions are explicit: one captured binder, terminal declaration, depth-two
collapse shape, and historical semantic witness in the SAME assignment. -/
namespace Yulang.GeneralDictionaryCheckedNonpointEvidence
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralDeclarations GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

theorem scope (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = []) :
    ∀ entry ∈ (generated registry state.context root declaration checked [(s.root,s.root)]).variables,
      entry.name ∉ declaration.outputNames → entry.name = s.binder := by
  unfold generated
  rw [terminal_requests _ _ _ _ _ _ terminal]
  exact GeneralDictionaryActualSchemaScope.root_input_name _ _ _ _ checked.scope s.binder names

theorem branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model :=
  GeneralDictionaryNonpointBranch.branch s registry root declaration checked queries names terminal
    (scope s registry root declaration checked names terminal) model old current

theorem current_instance (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Instance registry state.context model root declaration.id [])
    (current : GeneralNominalState.Models revision.snapshot model) :
    Instance registry (currentContext revision) model root declaration.id [] :=
  GeneralDictionaryNonpointEvidence.transport_instance s registry registryChecked root declaration visible checked
    queries names terminal located (scope s registry root declaration checked names terminal) model old current

theorem evidence (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Evidence registry state.context model root (.node declaration.id []))
    (current : GeneralNominalState.Models revision.snapshot model) :
    Evidence registry (currentContext revision) model root (.node declaration.id []) :=
  GeneralDictionaryNonpointEvidence.transport_evidence s registry registryChecked root declaration visible checked
    queries names terminal located (scope s registry root declaration checked names terminal) model old current

end Yulang.GeneralDictionaryCheckedNonpointEvidence
