import Yulang.GeneralNominalOpenReification
import Yulang.GeneralNominalFrontierValuations

/-! Real child materialization over simultaneous open capture labels. The
same substitution serves every variable occurrence; the emitter's second
normalization and compound input containment follow from the existing code. -/
namespace Yulang.GeneralNominalOpenChildProduction
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSaturationState
open GeneralNominalSharedCaptures GeneralNominalGroundProduction GeneralNominalGroundAccessibility
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalCanonicalTemplates GeneralNominalInspection
open GeneralNominalStructuralContainment GeneralNominalHeadMatchMass GeneralNominalTemplateSubstitution
open GeneralPatternNormalForm GeneralPatternVariableProvenance GeneralNominalChildAssembly
open GeneralNominalOpenPatternLabels

variable {model : GeneralNominalCommonBridge.Assignment}

theorem child_argument (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (generation : GenerationGuard tracked packet)
    (values : Nat → CommonNominalFullCarrier.Ty) (replacement : Nat → Expr Nat) (remaining : List Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (imagesClosed : ∀ name, Needed packet name → GeneralNominalHoleElimination.Closed remaining (replacement name))
    (meanings : ∀ name, Needed packet name → CaptureValue packet model name (denote values (replacement name))) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) :
    ∃ term, Label context
      (normalize ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture)) term ∧
      ArgumentValue packet model clause signature index (denote values term) ∧
      GeneralNominalHoleElimination.Closed remaining term := by
  classical
  let raw := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
  let template := normalize raw
  have templateMember : template ∈ normalizeArgs clause.arguments := by
    rw [normalize_map]
    exact List.mem_map.mpr ⟨raw,List.getElem_mem ..,rfl⟩
  have templateCovered : covered template = true := covered_member _
    (packet.checked.countsCovered clause present).2 template templateMember
  have used : Uses (Needed packet) template := fun name member =>
    ⟨clause,present,argument_variables _ template templateMember member⟩
  by_cases simple : ∃ name, template = .var name
  · obtain ⟨name,equal⟩ := simple
    have needed : Needed packet name := used name (by rw [equal]; exact List.mem_singleton_self _)
    obtain ⟨origin,usable⟩ := generation name needed
    refine ⟨replacement name,?_,Or.inl ⟨name,equal,meanings name needed,origin,usable⟩,imagesClosed name needed⟩
    change Label context (normalize (template.subst capture)) _
    rw [equal,Pattern.subst,label_normal (images name)]
    exact images name
  · have compound : ∀ name, template ≠ .var name := fun name equal => simple ⟨name,equal⟩
    have complete := GeneralNominalRequestCompleteness.input_complete state packet enabled clause present signature index compound
    have complete : Complete (translate context.state.constructors context.interpretation (normalize template)) := by
      simpa only [GeneralNominalCompoundEmission.lowerRequest,constructors,interpretation] using complete
    have normal := normalized template templateCovered
    have variables : Uses (Needed packet) (normalize template) := normalize_uses template used
    obtain ⟨openTerm,translated,canonical,leaves⟩ := quoted _ (translated_good (normalize template) normal complete variables)
    have filled := filled_label (context := context)
      (pattern := normalize template) (term := openTerm) ⟨covered_normal _ normal,translated.symm,canonical⟩
      capture replacement images
    refine ⟨openTerm.bind replacement,?_,Or.inr ⟨compound,openTerm,
      (fun name => denote values (replacement name)),canonical,
      (fun name member => meanings name (leaves name member)),?_,?_⟩,?_⟩
    · change Label context (normalize (template.subst capture)) _
      rw [GeneralPatternRecordSubstitution.normalize_template template templateCovered capture]
      exact filled
    · simpa only [GeneralNominalCompoundEmission.lowerRequest,constructors,interpretation] using translated.symm
    · exact (denote_bind openTerm replacement values).symm
    · intro hole member
      obtain ⟨name,present,member⟩ := (leaves_bind openTerm replacement hole).mp member
      exact imagesClosed name (leaves name present) hole member


/-- The head-wide bound counts all occurrences, including repeated variables
and every record field; the child descent is the checker's instantiated rule. -/
theorem list_mass (matched : GeneralNominalMatchedAssembly.Aligned
    (fun pattern label => ∃ term, Label context label term ∧
      Matches relation (translate context.state.constructors context.interpretation pattern) term) patterns labels)
    (covered : coveredArgs patterns = true) (capture : Nat → Pattern)
    (bounded : ∀ name term, relation name term → (normalize (capture name)).encode.size ≤ weight term) :
    GeneralNominalPatersonLineage.mass (substArgs capture patterns) ≤ GeneralNominalPatersonLineage.mass labels := by
  induction matched with
  | nil => exact Nat.le_refl _
  | @cons pattern label patterns labels known matched ih =>
    have parts : GeneralDeclarationPatterns.covered pattern = true ∧ coveredArgs patterns = true :=
      (Bool.and_eq_true ..).mp covered
    obtain ⟨term,label,matchHead⟩ := known
    have head := GeneralNominalOpenPatternLabels.instantiated_bound pattern parts.1
      (GeneralNominalMatchedAssembly.matches_complete matchHead) label matchHead capture bounded
    have tail := ih parts.2
    simp only [GeneralNominalPatersonLineage.mass,counted,substArgs,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] at head tail ⊢
    exact Nat.add_le_add head tail

theorem child_descent (packet : Packet roles)
    (matched : GeneralNominalMatchedAssembly.Aligned
      (fun pattern label => ∃ term, Label context label term ∧
        Matches relation (translate context.state.constructors context.interpretation pattern) term)
      (normalizeArgs packet.declaration.head) labels)
    (capture : Nat → Pattern)
    (bounded : ∀ name term, relation name term → (normalize (capture name)).encode.size ≤ weight term)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements) :
    GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs clause.arguments)) <
      GeneralNominalPatersonLineage.mass labels := by
  have head := list_mass matched (packet.checked.countsCovered clause present).1 capture bounded
  have descent := GeneralPatternConservativeSubstitution.checked_normalized_descent packet.checked clause present capture
  exact Nat.lt_of_lt_of_le descent head

end Yulang.GeneralNominalOpenChildProduction
