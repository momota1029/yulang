import Yulang.GeneralDictionaryNonterminalNonpointEvidence
import Yulang.GeneralDictionaryNonterminalScope
import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! Model-indexed nonterminal parent transport. Old semantic evidence supplies
its real BranchModels; new child evidence remains an explicit separate premise.
Changing capture bounds may change the emitted child demands, so we do not
reuse old child evidence by equating children. -/
namespace Yulang.GeneralDictionaryNonterminalNamedEvidence
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralDeclarations GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

open GeneralDictionaryNonterminalNonpointEvidence

/-- Current instance is derived in the same model. The old instance need not be
terminal; no child demands are silently identified across the revision. -/
theorem transport_instance (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (variables : GeneralDictionaryVariableWhereRequests.VariableInputs declaration)
    (outputs : GeneralDictionaryNonterminalScope.NormalizedOutputScope declaration)
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (oldChildren : List (GeneralSourceDictionaries.Occurrence roles))
    (old : Instance registry state.context model root declaration.id oldChildren)
    (current : GeneralNominalState.Models revision.snapshot model) :
    Instance registry (currentContext revision) model root declaration.id
      (currentChildren s registry root declaration checked) := by
  obtain ⟨selected,present,selectedChecked,key,role,bounds,found,done,ready,emitted,metadata,branch⟩ := old
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry registryChecked
    selected declaration present visible key
  subst selected
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  refine ⟨declaration,visible,checked,rfl,role,[(s.root,s.root)],located,?_,?_,rfl,metadata,?_⟩
  · exact (GeneralDictionaryCollapseReadiness.finished s declaration queries).2
  · exact (GeneralDictionaryRequestSnapshot.ready_revision revision registry root declaration checked _ _).mpr ready
  · exact GeneralDictionaryNonterminalScope.branch s registry root declaration checked queries names variables outputs model branch current

/-- Preserve a parent payload once evidence for the genuinely current emitted
children has independently been supplied. This is not the missing recursive
all-model invariant or a claim that the old children are unchanged. -/
theorem transport_evidence (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (variables : GeneralDictionaryVariableWhereRequests.VariableInputs declaration)
    (outputs : GeneralDictionaryNonterminalScope.NormalizedOutputScope declaration)
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (old : Evidence registry state.context model root (.node declaration.id dictionaries))
    (current : GeneralNominalState.Models revision.snapshot model)
    (children : CommonRoleOutermostResolver.All₂ (Evidence registry (currentContext revision) model)
      (currentChildren s registry root declaration checked) dictionaries) :
    Evidence registry (currentContext revision) model root (.node declaration.id dictionaries) := by
  obtain ⟨oldChildren,instanceRule,_⟩ := evidence_node_elim registry state.context model root declaration.id dictionaries old
  exact evidence_node registry (currentContext revision) model root declaration.id _ dictionaries
    (transport_instance s registry registryChecked root declaration visible checked queries names variables outputs located model oldChildren instanceRule current) children
end Yulang.GeneralDictionaryNonterminalNamedEvidence
