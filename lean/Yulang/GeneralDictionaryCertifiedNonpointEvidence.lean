import Yulang.GeneralDictionaryCheckedNonpointEvidence

/-! Certified revision supplies current source Models from the old journal model.
Historical Evidence is still explicit; this is not the missing universal
historical-recording invariant for arbitrary reachable selected nodes. -/
namespace Yulang.GeneralDictionaryCertifiedNonpointEvidence
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralDeclarations GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

theorem source_models (certified : Certified revision)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : GeneralNominalSaturationState.Models state model) :
    GeneralNominalState.Models revision.snapshot model :=
  ((certified.exact model).mpr old).1

theorem evidence (s : Shape revision) (certified : Certified revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (oldModel : GeneralNominalSaturationState.Models state model)
    (old : Evidence registry state.context model root (.node declaration.id [])) :
    GeneralNominalSaturationState.Models revision.result model ∧
    Evidence registry (currentContext revision) model root (.node declaration.id []) :=
  ⟨(certified.exact model).mpr oldModel,
    GeneralDictionaryCheckedNonpointEvidence.evidence s registry registryChecked root declaration visible checked
      queries names terminal located model old (source_models certified model oldModel)⟩
end Yulang.GeneralDictionaryCertifiedNonpointEvidence
