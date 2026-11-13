import Yulang.GeneralNominalNormalizedGround
import Yulang.GeneralNominalSimultaneousCaptures

/-! Factorization now needs only assembly of already shared finite labels:
head-wide multiplicity accounting and normalized child-template meanings.
Capture readback, including missing-origin fallback, is constructed here. -/
namespace Yulang.GeneralNominalCaptureAssembly
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalGroundAccessibility
open GeneralNominalSharedCaptures GeneralNominalSimultaneousCaptures
open GeneralNominalNormalizedGround
open GeneralNominalPatersonLineage (mass)

def Ready (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (model : GeneralNominalCommonBridge.Assignment) (capture : Nat → Pattern) : Prop :=
  (∀ name, normalize (capture name) = capture name) ∧
    (∀ name, ¬ Needed packet name → capture name = .var name) ∧
    ∀ name, Needed packet name → Meaning context packet model name (capture name) ∧
      ∀ origin, Usable packet name origin → ∀ pattern term,
        ClosedTerm context pattern term → At model .actual origin (denote (fun _ => .bottom) term) →
          mass [capture name] ≤ mass [pattern]

def NormalizedCaptureAssembly (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Prop :=
  ∀ (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles) (support : List (GeneralSourceDictionaries.Occurrence roles)),
    B4Target.Steps (Step registry root) (initial context root) state →
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    GeneralNominalActualInspectionSteps.PacketGuard state packet support →
    packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels →
      ∀ capture : Nat → Pattern, Ready context packet model capture →
        GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs packet.declaration.head)) ≤
          GeneralNominalPatersonLineage.mass labels ∧
        ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
          ∃ length : (substArgs capture (normalizeArgs clause.arguments)).length = (roles clause.role).arity,
            ∀ index : Fin (roles clause.role).arity, ∃ term,
              ClosedTerm context ((substArgs capture (normalizeArgs clause.arguments))[index.val]'(by rw [length]; exact index.isLt)) term ∧
              GeneralNominalGroundProduction.ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term)


theorem ready_captures (state : Tracked roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : GeneralNominalActualInspectionSteps.PacketGuard state packet support)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (branch : packet.Holds model) (known : Inputs context model packet.site labels) :
    ∃ capture, Ready context packet model capture := by
  obtain ⟨capture,normal,unused,shared⟩ := simultaneous state.current packet enabled.1.2.1.symm guard.2.1
    enabled.1.2.2.2.2.2.1 valid branch known guard.1.2.2.1
  exact ⟨capture,normal,unused,fun name needed => ⟨(shared name needed).1,(shared name needed).2.2⟩⟩

theorem factorization_of_assembly (assembly : NormalizedCaptureAssembly roles registry context root) :
    NormalizedCaptureFactorization roles registry context root := by
  intro state packet support trace constructors interpretation enabled guard nonempty model valid branch labels inputs
  obtain ⟨capture,ready⟩ := ready_captures state packet enabled guard model valid branch inputs
  exact ⟨capture,assembly state packet support trace constructors interpretation enabled guard nonempty
    model valid branch labels inputs capture ready⟩

theorem ground_accessible_of_assembly (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels)
    (assembly : NormalizedCaptureAssembly roles registry context root) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  accessible_of_reachable_factorization checked source point ground (factorization_of_assembly assembly)

end Yulang.GeneralNominalCaptureAssembly
