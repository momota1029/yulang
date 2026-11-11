import Yulang.GeneralDictionaryHeadlessRealization
import Yulang.GeneralDictionaryHeadlessPreparation

/-!
# Actual variable declarations in source dictionary evidence

The independent instance relation contains source demand intervals, actual
normalized head/RHS variables, binder values and the complete emitted children.
It contains no executable lookup, Located package, computed term vector or
arbitrary head/output meaning predicate. Its supported-variable scope remains
explicit; this is not nominal/compound pattern semantics or candidate selection.
-/
namespace Yulang.GeneralDictionaryHeadlessSourceEvidence
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries GeneralDictionaryTransactions
open GeneralSourceState (State Assignment Models)
open GeneralDictionaryVariableRealization (Realizes)
open GeneralDictionaryHeadlessRealization (values)
open GeneralDictionaryVariableHeads (heads)
variable {state : State}

/-- Independent partial source meaning for one actual declaration and all its
children. Every positional head and output RHS is an actual normalized variable. -/
def Instance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (assignment : Assignment) : LocalInstance registry.roles :=
  fun root key children =>
    ∃ declaration, ∃ present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      children = GeneralDictionaryEmissionPlans.children (frames root) root declaration
        (checked.2 declaration present) ∧
      ∃ binderValues : Nat → Common.Ty,
        Realizes declaration ((frames root).capture declaration.id) assignment binderValues ∧
        (∀ index : Fin (registry.roles root.demand.role).arity,
          ∃ pattern binder, declaration.head[index.val]? = some pattern ∧
            normalize pattern = .var binder ∧
            Common.Subtype (assignment (root.demand.arguments index).1).1 (binderValues binder) ∧
            Common.Subtype (binderValues binder) (assignment (root.demand.arguments index).2).1) ∧
        (∀ index : Fin root.demand.outputs.length,
          ∃ equation binder,
            GeneralDictionaryAssociatedProvenance.Supplies registry.roles declaration
              (root.demand.outputs[index]).name (.explicit equation) ∧
            normalize equation.rhs = .var binder ∧
            Common.Equivalent (assignment (root.demand.outputs[index]).target).1 (binderValues binder))

/-- Concrete source equations and actual head/RHS provenance produce the
independent binder-value instance without an externally supplied realization. -/
theorem source_instance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (assignment : Assignment)
    (root : Occurrence registry.roles) (key : Nat) (children : List (Occurrence registry.roles))
    (source : GeneralDictionaryVariableTransactions.SourceInstance registry checked frames
      (heads registry.roles state) assignment root key children) :
    Instance registry checked frames assignment root key children := by
  obtain ⟨declaration, present, identity, role, generated, located, head, outputs, holds⟩ :=
    GeneralDictionaryVariableTransactions.source_instance_declaration registry checked frames
      (heads registry.roles state) assignment root key children source
  have realized := GeneralDictionaryHeadlessRealization.realizes declaration (checked.2 declaration present)
    ((frames root).capture declaration.id) root.demand located.head head assignment
  refine ⟨declaration, present, identity, role, generated,
    values declaration ((frames root).capture declaration.id) assignment, realized, ?_, ?_⟩
  · intro index
    obtain ⟨pattern, binder, atIndex, normalized, meaning⟩ :=
      GeneralDictionaryVariableHeads.denotesAt_realization declaration ((frames root).capture declaration.id)
        assignment _ realized index.val (located.head index) (head.2.2 index)
    refine ⟨pattern, binder, atIndex, normalized, ?_, ?_⟩
    · exact Common.subtype_trans (holds.1 index).1 meaning.2
    · exact Common.subtype_trans meaning.1 (holds.1 index).2
  · intro index
    have denoted := (GeneralDictionaryVariableTerms.lookup_exact registry.roles declaration
      ((frames root).capture declaration.id) (checked.2 declaration present).identified.2.2.1 _ _).mp
      (outputs index)
    obtain ⟨equation, binder, supplied, normalized, meaning⟩ :=
      GeneralDictionaryVariableRealization.denotes_realization registry.roles declaration
        ((frames root).capture declaration.id) assignment _ realized _ _ denoted
    exact ⟨equation, binder, supplied, normalized,
      Common.equivalent_trans (holds.2 index) (Common.equivalent_symm meaning)⟩

/-- One fixed source dictionary works in every joint model. Neither head nor
output interpretation nor capture realization is supplied by the caller. -/
theorem prepare_uniform_source (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles)
    (recipe : GeneralDictionaryHeadlessPreparation.Recipe registry.roles state)
    (tree : Prepared registry.roles state)
    (success : GeneralDictionaryHeadlessPreparation.prepare registry checked frames recipe = some tree) :
    ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ assignment, Models (GeneralDictionaryBatchRecording.record tree.items) assignment →
        Evidence (Instance registry checked frames assignment) witness := by
  obtain ⟨witness, readback, uniform⟩ :=
    GeneralDictionaryHeadlessPreparation.prepare_uniform registry checked frames recipe tree success
  refine ⟨witness, readback, ?_⟩
  intro assignment model
  exact evidence_mono _ _
    (source_instance registry checked frames assignment) (uniform assignment model)

end Yulang.GeneralDictionaryHeadlessSourceEvidence
