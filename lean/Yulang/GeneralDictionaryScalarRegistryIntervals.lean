import Yulang.GeneralDictionaryScalarChildEvidence
import Yulang.GeneralDictionarySupportJournal

/-! A syntactic source-registry fragment suffices for variable/scalar child
interval formation. Actual traces preserve every packet's primitive
interpretation; no journal predicate or endpoint order is supplied by callers. -/
namespace Yulang.GeneralDictionaryScalarRegistryIntervals
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryScalarChildIntervals
variable {roles : Roles.RoleDecls}

theorem at_interpretation (registry : Registry) (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after) :
    after.context.interpretation = before.context.interpretation := by
  cases step with
  | reobserve => rfl
  | ordinary action =>
    cases action with
    | enqueue => rfl
    | install packet enabled novel =>
      change packet.context.interpretation = before.context.interpretation
      exact congrArg GeneralNominalCandidates.Context.interpretation enabled.1.2.1
    | merge => rfl
    | refresh focus after certificate => exact certificate.interpretation
    | equate => rfl

def InterpretationCoherent (state : State roles) : Prop :=
  ∀ packet ∈ state.packets, packet.context.interpretation = state.context.interpretation

theorem coherent_at (registry : Registry) (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (coherent : InterpretationCoherent before) : InterpretationCoherent after := by
  intro packet member
  rw [at_interpretation registry before after focus step]
  cases step with
  | reobserve => exact coherent packet member
  | ordinary action =>
    cases action with
    | enqueue => exact coherent packet member
    | merge => exact coherent packet member
    | refresh => exact coherent packet member
    | equate => exact coherent packet member
    | install installed enabled novel =>
      change packet ∈ installed :: before.packets at member
      rcases List.mem_cons.mp member with rfl | member
      · exact congrArg GeneralNominalCandidates.Context.interpretation enabled.1.2.1
      · exact coherent packet member

theorem coherent_trace (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (coherent : InterpretationCoherent before) : InterpretationCoherent after := by
  induction path with
  | refl => exact coherent
  | tail _ step ih => exact coherent_at registry _ _ _ step.choose_spec.2 ih

theorem reachable_coherent {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    InterpretationCoherent state.current := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  apply coherent_trace registry root (initial context root) state.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry root _ _ path)
  intro packet member
  cases member

def ScalarVariableRegistry (registry : Registry) (interpretation : GeneralNominalInspection.Interpretation) : Prop :=
  ∀ declaration ∈ registry.declarations, ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
    (∃ name, GeneralDeclarationPatterns.normalize pattern = .var name) ∨
    (∃ key base, GeneralDeclarationPatterns.normalize pattern = .app key [] ∧
      interpretation.primitives key = some (.scalar base))

theorem journal {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (fragment : ScalarVariableRegistry registry state.current.context.interpretation)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    ScalarVariableJournal state := by
  intro packet member clause declared signature index
  have formed := GeneralNominalDownstreamSteps.formed_old
    (GeneralNominalValueSteps.formed_old (GeneralNominalValueBoundary.reachable_formed registry state root reachable))
  have visible := GeneralDictionarySupportJournal.packet_visible registry root state formed packet member
  have result := fragment packet.declaration visible clause declared _ (List.getElem_mem (by rw [signature.1]; exact index.isLt))
  rcases result with varCase | ⟨key,base,shape,primitive⟩
  · exact Or.inl varCase
  · exact Or.inr ⟨key,base,shape,by rw [reachable_coherent reachable packet member]; exact primitive⟩

theorem generated_intervals {registry : Registry} {root child : Occurrence roles} {state : Tracked roles}
    (fragment : ScalarVariableRegistry registry state.current.context.interpretation)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (reached : Generated state.current root child)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) (index) :
    CommonNominalFullCarrier.Subtype (model (child.demand.arguments index).1).1
      (model (child.demand.arguments index).2).1 :=
  GeneralDictionaryScalarChildIntervals.generated_intervals reachable (journal fragment reachable) reached model valid index

theorem selected_instance (registry : Registry) (original root : Occurrence roles)
    (state : Tracked roles) (fragment : ScalarVariableRegistry registry state.current.context.interpretation)
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
  GeneralDictionaryScalarChildEvidence.selected_instance registry original root state reachable
    (journal fragment reachable) reached declaration visible checked shape supported key children selected model valid

end Yulang.GeneralDictionaryScalarRegistryIntervals
