import Yulang.GeneralDictionaryProvenanceGeneratedIntervals
import Yulang.GeneralDictionarySupportJournal

/-! Source-fragment sufficient condition for generated interval formation. The
actual trace establishes registry visibility of every stored packet; users do
not supply a separate journal invariant or capture-presence proof. -/
namespace Yulang.GeneralDictionaryVariableRegistryIntervals
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralDictionaryGeneratedIntervals GeneralDictionaryCapturedChildIntervals
variable {roles : Roles.RoleDecls}

/-- Each unnamed argument of each source where clause normalizes to a variable.
Named outputs and declaration heads are unrestricted by this predicate. -/
def VariableRegistry (registry : Registry) : Prop :=
  ∀ declaration ∈ registry.declarations, ∀ clause ∈ declaration.requirements,
    ∀ pattern ∈ clause.arguments, ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name

theorem journal {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (fragment : VariableRegistry registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    VariableJournal state := by
  intro packet member clause declared signature index
  have formed := GeneralNominalDownstreamSteps.formed_old
    (GeneralNominalValueSteps.formed_old (GeneralNominalValueBoundary.reachable_formed registry state root reachable))
  have visible := GeneralDictionarySupportJournal.packet_visible registry root state formed packet member
  exact fragment packet.declaration visible clause declared _ (List.getElem_mem _)

theorem generated_intervals {registry : Registry} {root child : Occurrence roles} {state : Tracked roles}
    (fragment : VariableRegistry registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (reached : Generated state.current root child)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) (index) :
    CommonNominalFullCarrier.Subtype (model (child.demand.arguments index).1).1
      (model (child.demand.arguments index).2).1 :=
  GeneralDictionaryGeneratedIntervals.generated_intervals reachable (journal fragment reachable) reached model valid index

theorem selected_instance (registry : Registry) (original root : Occurrence roles)
    (state : Tracked roles) (fragment : VariableRegistry registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry original state)
    (reached : Generated state.current original root)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionaryScalarIntervalInspection.Shape state.current.context root declaration)
    (supported : GeneralDictionaryRequestProvenance.Supported registry original state
      (GeneralNominalMaterialization.requests state.current.context.state registry root declaration checked
        (GeneralNominalRecursiveInspection.bindings state.current.context.state
          (GeneralNominalRecursiveCandidates.report state.current.context declaration
            (GeneralDictionaryScalarIntervalInspection.intervals shape.entries)))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model root key children :=
  GeneralDictionaryProvenanceGeneratedIntervals.selected_instance registry original root state reachable
    (journal fragment reachable) reached declaration visible checked shape supported key children selected model valid

end Yulang.GeneralDictionaryVariableRegistryIntervals
