import Yulang.GeneralDictionaryNonterminalRecordedRevision
import Yulang.GeneralDictionaryVariableLeafPlans

/-! An end-to-end restricted journal bridge for arbitrary finite terminal leaf
children. The prior trace supplies the parent Instance; declarative current leaf
plans supply child Evidence. Neither old parent Evidence nor current child
Evidence is assumed. Location, query shape and endpoint ordering in plans remain
explicit, and unrestricted Value/I-26 execution is not asserted. -/
namespace Yulang.GeneralDictionaryRecordedLeafPlans
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {before : State roles} {revision : Revision before}

theorem evidence_from_leaf_plans (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (saturationRoot : Occurrence roles)
    (initialContext : Context)
    (path : B4Target.Steps (GeneralDictionaryRecordedRevisionTrace.Step registry saturationRoot)
      (initial initialContext saturationRoot) before)
    (certificate : Certified revision)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (key : packet.declaration.id = declaration.id)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries before.context.state before.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (located : arguments before.context packet.site.occurrence = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models revision.result model)
    (keys : List Nat)
    (plans : CommonRoleOutermostResolver.All₂
      (fun child key => Nonempty (GeneralDictionaryVariableLeafPlans.LeafPlan registry
        (currentContext revision) model child key))
      (GeneralDictionaryNonterminalNonpointEvidence.currentChildren s registry packet.site.occurrence declaration checked)
      keys) :
    Evidence registry (currentContext revision) model packet.site.occurrence
      (.node declaration.id (keys.map fun key => .node key [])) := by
  have parent := GeneralDictionaryNonterminalRecordedRevision.instance_from_trace s registry registryChecked
    saturationRoot initialContext path certificate packet recorded declaration visible key checked queries names
    variables located model valid
  have metadata : Metadata registry (currentContext revision) := by
    obtain ⟨selected,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := parent
    exact metadata
  exact GeneralDictionaryVariableLeafPlans.parent_evidence registry (currentContext revision) model metadata valid.1
    packet.site.occurrence declaration.id _ keys parent plans
end Yulang.GeneralDictionaryRecordedLeafPlans
