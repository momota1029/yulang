import Yulang.GeneralDictionaryNonterminalNonpointEvidence
import Yulang.GeneralDictionaryRecordedRevisionTrace

/-! A report-changing nonterminal revision after an actual restricted journal
trace. Historical Instance is derived from the trace invariant, not supplied as
a semantic premise. The path trace retains its explicit report-preservation
restrictions; only the last depth-two collapse may change captures and child
demands. New child Evidence is still a separate obligation. -/
namespace Yulang.GeneralDictionaryNonterminalRecordedRevision
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls} {before : State roles} {revision : Revision before}

/-- Every model of the revised journal receives the recomputed parent Instance.
No semantic old BranchModels/Instance assumption is required from the caller. -/
theorem instance_from_trace (s : Shape revision) (registry : Registry)
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
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models revision.result model) :
    Instance registry (currentContext revision) model packet.site.occurrence declaration.id
      (GeneralDictionaryNonterminalNonpointEvidence.currentChildren s registry packet.site.occurrence declaration checked) := by
  have earlier : Models before model := (certificate.exact model).mp valid
  have old := GeneralDictionaryRecordedRevisionTrace.initial_trace_current
    registry saturationRoot initialContext before path packet recorded model earlier
  rw [key] at old
  exact GeneralDictionaryNonterminalNonpointEvidence.transport_instance s registry registryChecked
    packet.site.occurrence declaration visible checked queries names variables located model packet.children old valid.1

/-- The same final journal model validates the parent once each genuinely
current child is independently evidenced. This does not reuse the old children
or extend the path invariant to unrestricted Value steps. -/
theorem evidence_from_trace (s : Shape revision) (registry : Registry)
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
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂ (Evidence registry (currentContext revision) model)
      (GeneralDictionaryNonterminalNonpointEvidence.currentChildren s registry packet.site.occurrence declaration checked)
      dictionaries) :
    Evidence registry (currentContext revision) model packet.site.occurrence (.node declaration.id dictionaries) :=
  evidence_node registry (currentContext revision) model packet.site.occurrence declaration.id _ dictionaries
    (instance_from_trace s registry registryChecked saturationRoot initialContext path certificate packet recorded
      declaration visible key checked queries names variables located model valid) children
end Yulang.GeneralDictionaryNonterminalRecordedRevision
