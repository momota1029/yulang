import YulangClosure.CanonicalLiteralGeneratorR236
import YulangClosure.OriginalSourceGeneration

/-!
R240's revised constructor model. Generation is a direct equation over
the raw payload and source coordinates. Satisfaction is an independent record
of endpoint equalities; it does not inspect source typing, Kernel.atom, or a
native solver result. The original source leaf below consumes the same
assignment. This is a literal-constructor model, not a complete SourceProblem
instance and not a Rust correspondence theorem.
-/
namespace YulangClosure.OriginalLiteralSolutionModelR240

open OriginalSource
open CanonicalLiteralGeneratorR236

abbrev IntrinsicEffect := List OriginalSource.Declaration

structure GenerationContext (Root Event Scope Witness : Type) where
  site : OriginalSource.Site
  syntaxContext : OriginalSource.Context
  root : Root
  event : Event
  scope : Scope
  witness : Witness

structure LiteralConstraint (Root Event Scope Witness : Type) where
  context : GenerationContext Root Event Scope Witness
  literal : OriginalSource.Literal
  synthesis : PaperTypes.Ty
  finalRoot : PaperTypes.Ty
  value : PaperTypes.Value
  intrinsicEffect : IntrinsicEffect
  root : Root
  event : Event
  scope : Scope
  witness : Witness

/-- Adopted direct all-eight generator. The two type endpoints remain
distinct data fields, and writtenTarget is not assigned by this base rule. -/
def generate {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal) : LiteralConstraint Root Event Scope Witness :=
  { context := context
    literal := literal
    synthesis := generateType literal
    finalRoot := generateType literal
    value := generateValue literal
    intrinsicEffect := []
    root := context.root
    event := context.event
    scope := context.scope
    witness := context.witness }

structure LiteralAssignment (Root Event Scope Witness : Type) where
  descriptor : OriginalSource.Endpoint → PaperTypes.Ty
  value : OriginalSource.Endpoint → PaperTypes.Value
  root : Root
  event : Event
  scope : Scope
  witness : Witness

def synthesisEndpoint {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness) : OriginalSource.Endpoint :=
  ⟨context.site, .synthesis⟩

def finalRootEndpoint {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness) : OriginalSource.Endpoint :=
  ⟨context.site, .finalRoot⟩

def writtenTargetEndpoint {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness) : OriginalSource.Endpoint :=
  ⟨context.site, .writtenTarget⟩

/-- Satisfaction of the generated canonical coordinates. The written-target
port is deliberately unconstrained by literal base introduction. -/
def Satisfies {Root Event Scope Witness : Type}
    (constraint : LiteralConstraint Root Event Scope Witness)
    (assignment : LiteralAssignment Root Event Scope Witness) : Prop :=
  assignment.descriptor (synthesisEndpoint constraint.context) = constraint.synthesis ∧
  assignment.descriptor (finalRootEndpoint constraint.context) = constraint.finalRoot ∧
  assignment.value (finalRootEndpoint constraint.context) = constraint.value ∧
  assignment.root = constraint.root ∧
  assignment.event = constraint.event ∧
  assignment.scope = constraint.scope ∧
  assignment.witness = constraint.witness ∧
  constraint.intrinsicEffect = []

structure OriginalLiteralRow (Root Event : Type) where
  descriptor : PaperTypes.Ty
  value : PaperTypes.Value
  root : Root
  event : Event

def sourceLiteralRow {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (assignment : LiteralAssignment Root Event Scope Witness) : OriginalLiteralRow Root Event :=
  ⟨assignment.descriptor (finalRootEndpoint context),
    assignment.value (finalRootEndpoint context), assignment.root, assignment.event⟩

structure IntrinsicReturn (Root Event : Type) where
  effect : IntrinsicEffect
  resultType : PaperTypes.Ty
  value : PaperTypes.Value
  root : Root
  event : Event

def generatedReturn {Root Event Scope Witness : Type}
    (constraint : LiteralConstraint Root Event Scope Witness) : IntrinsicReturn Root Event :=
  ⟨constraint.intrinsicEffect, constraint.finalRoot, constraint.value,
    constraint.root, constraint.event⟩

theorem generated_canonical_payload {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal) :
    let constraint := generate context literal
    constraint.synthesis = PaperTypes.literalType (toPaperLiteral literal) ∧
    constraint.finalRoot = PaperTypes.literalType (toPaperLiteral literal) ∧
    constraint.value = PaperTypes.Value.literal (toPaperLiteral literal) ∧
    constraint.intrinsicEffect = [] := by
  simp [generate, generateType_matches_adopted_l1, generateValue_matches_adopted_l1]

theorem every_solution_reads_original_literal_row {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal)
    (assignment : LiteralAssignment Root Event Scope Witness)
    (solves : Satisfies (generate context literal) assignment) :
    sourceLiteralRow context assignment =
      ⟨PaperTypes.literalType (toPaperLiteral literal),
        PaperTypes.Value.literal (toPaperLiteral literal),
        context.root, context.event⟩ := by
  rcases solves with ⟨_, finalType, payload, root, event, _, _, _⟩
  have typeReadout :
      assignment.descriptor ⟨context.site, .finalRoot⟩ =
        PaperTypes.literalType (toPaperLiteral literal) := by
    simpa [generate, finalRootEndpoint, generateType_matches_adopted_l1] using finalType
  have valueReadout :
      assignment.value ⟨context.site, .finalRoot⟩ =
        PaperTypes.Value.literal (toPaperLiteral literal) := by
    simpa [generate, finalRootEndpoint, generateValue_matches_adopted_l1] using payload
  have rootReadout : assignment.root = context.root := by
    simpa [generate] using root
  have eventReadout : assignment.event = context.event := by
    simpa [generate] using event
  simp [sourceLiteralRow, finalRootEndpoint, typeReadout, valueReadout,
    rootReadout, eventReadout]

theorem generated_return_is_l1_pure_return {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal) :
    generatedReturn (generate context literal) =
      ⟨[], PaperTypes.literalType (toPaperLiteral literal),
        PaperTypes.Value.literal (toPaperLiteral literal), context.root, context.event⟩ := by
  simp [generatedReturn, generate, generateType_matches_adopted_l1,
    generateValue_matches_adopted_l1]

/-- Independent local L1 interpretation consumed by the original
`literalDeclaration` atom. It is a relation on raw assignment data, not a
source judgment or a successful-checking premise. -/
def originalLiteralDeclaration {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (assignment : LiteralAssignment Root Event Scope Witness)
    (atom : OriginalSource.Atom) : Prop :=
  ∃ literal, atom.literal = some literal ∧ atom.site = context.site ∧
    atom.context = context.syntaxContext ∧
    sourceLiteralRow context assignment =
      ⟨PaperTypes.literalType (toPaperLiteral literal),
        PaperTypes.Value.literal (toPaperLiteral literal),
        context.root, context.event⟩

theorem generated_solution_satisfies_original_declaration {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal)
    (assignment : LiteralAssignment Root Event Scope Witness)
    (solves : Satisfies (generate context literal) assignment)
    (atom : OriginalSource.Atom)
    (payload : atom.literal = some literal)
    (site : atom.site = context.site)
    (syntaxContext : atom.context = context.syntaxContext) :
    originalLiteralDeclaration context assignment atom := by
  refine ⟨literal, payload, site, syntaxContext, ?_⟩
  exact every_solution_reads_original_literal_row context literal assignment solves

theorem generated_return_effect_is_intrinsically_empty
    {Root Event Scope Witness : Type}
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal) :
    (generatedReturn (generate context literal)).effect = [] := rfl

/-- This constructor-specific update changes only the selected literal atom.
Every unrelated source/local operation, including checking and conversion,
is retained from the supplied original kernel. -/
def literalKernel {Root Event Scope Witness : Type}
    (original : OriginalSource.Kernel (LiteralAssignment Root Event Scope Witness))
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal) :
    OriginalSource.Kernel (LiteralAssignment Root Event Scope Witness) :=
  { original with atom := fun environment atom =>
      if atom.kind = .literalDeclaration ∧ atom.site = context.site ∧
        atom.context = context.syntaxContext ∧ atom.literal = some literal
      then originalLiteralDeclaration context environment.root atom
      else original.atom environment atom }

/-- Exact source rule tree generated for the unannotated literal constructor.
The atom is the one consumed by the original `.lit` rule. -/
theorem unannotated_literal_rule_tree
    (context : OriginalSource.Context) (site : OriginalSource.Site)
    (literal : OriginalSource.Literal) :
    OriginalSource.sourceRules context (.literal ⟨site, none⟩ literal) =
      .rule .lit site context
        [.atom (CanonicalSourceInferenceModelR196.literalObligation context site literal)] .nil := by
  simp only [OriginalSource.sourceRules,
    CanonicalSourceInferenceModelR196.literalObligation, OriginalSource.atom]
  rfl

/-- Apply the generated arbitrary-solution readout in the actual original
literal rule. The same environment root is used for generation satisfaction
and the original local atom; no `LiteralAtom`, source judgment, or native
success premise is supplied. -/
theorem generated_solution_consumed_by_original_literal_rule
    {Root Event Scope Witness : Type}
    (original : OriginalSource.Kernel (LiteralAssignment Root Event Scope Witness))
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal)
    (environment : OriginalSource.Environment (LiteralAssignment Root Event Scope Witness))
    (solves : Satisfies (generate context literal) environment.root) :
    OriginalSource.Judgment (literalKernel original context literal) environment
      (OriginalSource.sourceRules context.syntaxContext
        (.literal ⟨context.site, none⟩ literal)) := by
  rw [unannotated_literal_rule_tree context.syntaxContext context.site literal]
  apply OriginalSource.Judgment.rule
  · intro premise member
    simp only [List.mem_singleton] at member
    subst premise
    apply OriginalSource.Local.atom
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    exact generated_solution_satisfies_original_declaration
      context literal environment.root solves _ rfl rfl rfl
  · exact OriginalSource.Judgments.nil

/-- Formula-level consumer equation for the same actual source literal node. -/
theorem generated_solution_consumed_by_original_build
    {Root Event Scope Witness : Type}
    (original : OriginalSource.Kernel (LiteralAssignment Root Event Scope Witness))
    (context : GenerationContext Root Event Scope Witness)
    (literal : OriginalSource.Literal)
    (environment : OriginalSource.Environment (LiteralAssignment Root Event Scope Witness))
    (solves : Satisfies (generate context literal) environment.root) :
    OriginalSource.Satisfies (literalKernel original context literal) environment
      (OriginalSource.Build context.syntaxContext
        (.literal ⟨context.site, none⟩ literal)) := by
  exact (OriginalSource.reconstruction (literalKernel original context literal) environment
    (OriginalSource.sourceRules context.syntaxContext
      (.literal ⟨context.site, none⟩ literal))).2
      (generated_solution_consumed_by_original_literal_rule original context literal environment solves)

#check @generated_canonical_payload
#print axioms generated_canonical_payload
#check @every_solution_reads_original_literal_row
#print axioms every_solution_reads_original_literal_row
#check @generated_return_is_l1_pure_return
#print axioms generated_return_is_l1_pure_return
#check @generated_solution_satisfies_original_declaration
#print axioms generated_solution_satisfies_original_declaration
#check @unannotated_literal_rule_tree
#print axioms unannotated_literal_rule_tree
#check @generated_solution_consumed_by_original_literal_rule
#print axioms generated_solution_consumed_by_original_literal_rule
#check @generated_solution_consumed_by_original_build
#print axioms generated_solution_consumed_by_original_build
#check @generated_return_effect_is_intrinsically_empty
#print axioms generated_return_effect_is_intrinsically_empty

end YulangClosure.OriginalLiteralSolutionModelR240
