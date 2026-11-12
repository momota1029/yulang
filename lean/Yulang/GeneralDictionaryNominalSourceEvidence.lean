import Yulang.GeneralDictionaryNominalEquations
import Yulang.GeneralDictionaryPayloadPreparation

/-!
# Actual declaration evidence for arbitrary full nominal models

Supported variable heads and RHS terms retain their actual declaration provenance.
Captures and source frames remain explicit. Neither candidate selection, general
compound-pattern materialization, nor source readiness is established here.
-/
namespace Yulang.GeneralDictionaryNominalSourceEvidence
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries GeneralDictionaryStateEquations
open GeneralDictionaryTransactions (Frames Prepared PlannedAt LiftedTerms)
open GeneralDictionaryVariableHeads (heads HeadDenotes)
open GeneralNominalCommonBridge (Assignment Models)
open GeneralDictionaryNominalEquations (Holds)
open Core.PresenceGeneration (TyTerm)
variable {state : GeneralSourceState.State}

def Realizes (declaration : Declaration) (capture : Capture)
    (assignment : Assignment) (values : Nat → CommonNominalFullCarrier.Ty) : Prop :=
  (∀ binder ∈ declaration.inputNames,
    CommonNominalFullCarrier.Subtype (assignment (capture.inputs binder).1).1 (values binder) ∧
    CommonNominalFullCarrier.Subtype (values binder) (assignment (capture.inputs binder).2).1) ∧
  (∀ binder ∈ declaration.outputNames,
    CommonNominalFullCarrier.Equivalent (values binder) (assignment (capture.outputs binder)).1)

def values (declaration : Declaration) (capture : Capture) (assignment : Assignment) :
    Nat → CommonNominalFullCarrier.Ty :=
  fun binder => if binder ∈ declaration.outputNames then (assignment (capture.outputs binder)).1
    else (assignment (capture.inputs binder).1).1

theorem realizes (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (capture : Capture)
    (demand : GeneralSourceState.Demand roles)
    (head : Fin (roles demand.role).arity → TyTerm (Fin state.slots))
    (denoted : HeadDenotes declaration capture demand head) (assignment : Assignment) :
    Realizes declaration capture assignment (values declaration capture assignment) := by
  constructor
  · intro binder input
    obtain ⟨same, notOutput⟩ := GeneralDictionaryHeadlessRealization.supported_input
      declaration checked capture demand head denoted binder input
    simp only [values, notOutput, ← same]
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · intro binder output
    simp only [values, output]
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

theorem singleton_value (capture : Capture) (assignment : Assignment)
    (binder : Nat) (value : CommonNominalFullCarrier.Ty)
    (same : (capture.inputs binder).1 = (capture.inputs binder).2)
    (inside : CommonNominalFullCarrier.Subtype (assignment (capture.inputs binder).1).1 value ∧
      CommonNominalFullCarrier.Subtype value (assignment (capture.inputs binder).2).1) :
    CommonNominalFullCarrier.Equivalent value (assignment (capture.inputs binder).1).1 := by
  rw [← same] at inside
  exact ⟨inside.2, inside.1⟩

theorem head_realization (declaration : Declaration) (capture : Capture)
    (assignment : Assignment) (values : Nat → CommonNominalFullCarrier.Ty)
    (realized : Realizes declaration capture assignment values)
    (index : Nat) (term : TyTerm (Fin state.slots))
    (denoted : GeneralDictionaryVariableHeads.DenotesAt state declaration capture index term) :
    ∃ pattern binder, declaration.head[index]? = some pattern ∧ normalize pattern = .var binder ∧
      CommonNominalFullCarrier.Equivalent (values binder)
        ((liftType state term).eval CommonNominalFullCarrier.model assignment) := by
  obtain ⟨pattern, binder, slot, present, normalized, input, same, source, rfl⟩ := denoted
  refine ⟨pattern, binder, present, normalized, ?_⟩
  change CommonNominalFullCarrier.Equivalent (values binder) (assignment (state.source slot)).1
  rw [source]
  exact singleton_value capture assignment binder (values binder) same (realized.1 binder input)

theorem output_realization (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (assignment : Assignment) (values : Nat → CommonNominalFullCarrier.Ty)
    (realized : Realizes declaration capture assignment values) (name : Nat) (term : TyTerm Nat)
    (denoted : GeneralDictionaryVariableTerms.Denotes roles declaration capture name term) :
    ∃ equation binder, GeneralDictionaryAssociatedProvenance.Supplies roles declaration name (.explicit equation) ∧
      normalize equation.rhs = .var binder ∧
      CommonNominalFullCarrier.Equivalent (values binder) (term.eval CommonNominalFullCarrier.model assignment) := by
  obtain ⟨equation, binder, supplied, normalized, source⟩ := denoted
  refine ⟨equation, binder, supplied, normalized, ?_⟩
  rcases source with ⟨output, rfl⟩ | ⟨_, input, same, rfl⟩
  · exact realized.2 binder output
  · exact singleton_value capture assignment binder (values binder) same (realized.1 binder input)

/-- Independent supported-variable declaration meaning in the full nominal carrier. -/
def Instance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (assignment : Assignment) : LocalInstance registry.roles :=
  fun root key children =>
    ∃ declaration, ∃ present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      children = GeneralDictionaryEmissionPlans.children (frames root) root declaration
        (checked.2 declaration present) ∧
      ∃ binderValues : Nat → CommonNominalFullCarrier.Ty,
        Realizes declaration ((frames root).capture declaration.id) assignment binderValues ∧
        (∀ index : Fin (registry.roles root.demand.role).arity,
          ∃ pattern binder, declaration.head[index.val]? = some pattern ∧
            normalize pattern = .var binder ∧
            CommonNominalFullCarrier.Subtype (assignment (root.demand.arguments index).1).1 (binderValues binder) ∧
            CommonNominalFullCarrier.Subtype (binderValues binder) (assignment (root.demand.arguments index).2).1) ∧
        (∀ index : Fin root.demand.outputs.length,
          ∃ equation binder,
            GeneralDictionaryAssociatedProvenance.Supplies registry.roles declaration
              (root.demand.outputs[index]).name (.explicit equation) ∧
            normalize equation.rhs = .var binder ∧
            CommonNominalFullCarrier.Equivalent (assignment (root.demand.outputs[index]).target).1 (binderValues binder))

/-- Plan, computed provenance and nominal equations share one checked declaration. -/
theorem source_instance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (assignment : Assignment)
    (root : Occurrence registry.roles) (key : Nat) (children : List (Occurrence registry.roles))
    (located : Located state root.demand)
    (plan : GeneralDictionaryEmissionPlans.Plan registry checked (frames root) root key children)
    (terms : GeneralDictionaryVariablePlans.Terms registry frames (heads registry.roles state) root key located)
    (holds : Holds located.equations assignment) : Instance registry checked frames assignment root key children := by
  obtain ⟨first, firstPresent, firstKey, _, generated⟩ := plan
  obtain ⟨declaration, present, identity, role, head, outputs⟩ := terms
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked first declaration
    firstPresent present (firstKey.trans identity.symm)
  subst first
  have realized := realizes declaration (checked.2 declaration present)
    ((frames root).capture declaration.id) root.demand located.head head assignment
  refine ⟨declaration, present, identity, role, generated,
    values declaration ((frames root).capture declaration.id) assignment, realized, ?_, ?_⟩
  · intro index
    obtain ⟨pattern, binder, atIndex, normalized, meaning⟩ := head_realization declaration
      ((frames root).capture declaration.id) assignment _ realized index.val (located.head index) (head.2.2 index)
    exact ⟨pattern, binder, atIndex, normalized,
      CommonNominalFullCarrier.subtype_trans (holds.1 index).1 meaning.2,
      CommonNominalFullCarrier.subtype_trans meaning.1 (holds.1 index).2⟩
  · intro index
    have denoted := (GeneralDictionaryVariableTerms.lookup_exact registry.roles declaration
      ((frames root).capture declaration.id) (checked.2 declaration present).identified.2.2.1 _ _).mp (outputs index)
    obtain ⟨equation, binder, supplied, normalized, meaning⟩ := output_realization registry.roles declaration
      ((frames root).capture declaration.id) assignment _ realized _ _ denoted
    exact ⟨equation, binder, supplied, normalized,
      CommonNominalFullCarrier.subtype_trans (holds.2 index).1 meaning.2,
      CommonNominalFullCarrier.subtype_trans meaning.1 (holds.2 index).2⟩

/-- Syntactic storage yields actual declaration evidence in each nominal model. -/
theorem transaction_evidence (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (tree : Prepared registry.roles state)
    (built : GeneralDictionaryVariableTransactions.Built registry checked frames (heads registry.roles state) tree)
    (assignment : Assignment) (model : Models (GeneralDictionaryBatchRecording.record tree.items) assignment) :
    Evidence (Instance registry checked frames assignment) tree.dictionary := by
  have stored := GeneralDictionaryVariableTransactions.transaction_stored registry checked frames
    (heads registry.roles state) tree built
  apply evidence_mono _ _ ?_ stored
  intro root key children instanceRule
  obtain ⟨located, ⟨plan, original, terms, same⟩, recorded⟩ := instanceRule
  subst located
  have holds := GeneralDictionaryNominalEquations.recorded_holds _ recorded assignment model
  rw [GeneralDictionaryBatchRecording.relocate_equations] at holds
  exact source_instance registry checked frames assignment root key children original plan terms holds

/-- The prepared tree itself is a fixed witness for the original raw payload. -/
theorem prepare_uniform_source (registry : Registry) (checked : Checked registry)
    (state : GeneralSourceState.State) (frames : Frames registry.roles)
    (payload : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked state frames payload root = some tree) :
    ∃ witness, Readback root payload witness ∧
      ∀ assignment, Models (GeneralDictionaryBatchRecording.record tree.items) assignment →
        Evidence (Instance registry checked frames assignment) witness := by
  obtain ⟨source, _, prepared⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry checked state frames payload root tree).mp success
  obtain ⟨localized, _, built⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry checked state frames _ tree).mp prepared
  refine ⟨tree.dictionary,
    GeneralDictionaryPayloadPreparation.prepare_readback registry checked state frames payload root tree success, ?_⟩
  exact transaction_evidence registry checked frames tree
    (GeneralDictionaryHeadlessPreparation.prepare_built registry checked frames localized tree built)

end Yulang.GeneralDictionaryNominalSourceEvidence
