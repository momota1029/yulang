import Yulang.GeneralDictionaryNonpointBranch
import Yulang.GeneralDictionaryCollapseReadiness
import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! Model-indexed terminal evidence after nonpoint capture collapse. The old
branch equations are a real premise, not inferred from reachability/selection.
No point bounds are imposed on the retained or discarded leaf intervals. -/
namespace Yulang.GeneralDictionaryNonpointEvidence
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralDeclarations GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

/-- Preserve a terminal source instance in the SAME assignment. This does not
promote an existential old branch witness to all current-state models. -/
theorem transport_instance (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (located : arguments state.context root = some [(s.root,s.root)])
    (scope : ∀ entry ∈ (generated registry state.context root declaration checked [(s.root,s.root)]).variables,
      entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Instance registry state.context model root declaration.id [])
    (current : GeneralNominalState.Models revision.snapshot model) :
    Instance registry (currentContext revision) model root declaration.id [] := by
  obtain ⟨selected,present,selectedChecked,key,role,bounds,found,done,ready,emitted,metadata,branch⟩ := old
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry registryChecked
    selected declaration present visible key
  subst selected
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  refine ⟨declaration,visible,checked,rfl,role,[(s.root,s.root)],?_,?_,?_,?_,metadata,?_⟩
  · exact located
  · exact (GeneralDictionaryCollapseReadiness.finished s declaration queries).2
  · exact (GeneralDictionaryCollapseReadiness.ready_same s registry root declaration checked terminal).mpr ready
  · exact (GeneralDictionaryLinearLeaf.children_empty (currentContext revision) registry root declaration checked terminal _).symm
  · exact GeneralDictionaryNonpointBranch.branch s registry root declaration checked queries names terminal scope model branch current

/-- Existing erased terminal Evidence transports via its actual old Instance.
The conclusion is model-indexed; reachable or Stable alone are not premises
substituting for the historical semantic witness. -/
theorem transport_evidence (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (located : arguments state.context root = some [(s.root,s.root)])
    (scope : ∀ entry ∈ (generated registry state.context root declaration checked [(s.root,s.root)]).variables,
      entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : Evidence registry state.context model root (.node declaration.id []))
    (current : GeneralNominalState.Models revision.snapshot model) :
    Evidence registry (currentContext revision) model root (.node declaration.id []) := by
  apply (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff ..).mpr
  apply transport_instance s registry registryChecked root declaration visible checked queries names terminal located scope model
  · exact (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff ..).mp old
  · exact current

end Yulang.GeneralDictionaryNonpointEvidence
