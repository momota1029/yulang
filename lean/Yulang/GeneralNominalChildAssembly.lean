import Yulang.GeneralNominalClosedSubstitution

/-! Closed child labels are constructed from actual candidate preparation
and shared finite captures, without an additional assembly hypothesis. -/
namespace Yulang.GeneralNominalChildAssembly
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSaturationState
open GeneralNominalSharedCaptures GeneralNominalCaptureAssembly GeneralNominalSimultaneousCaptures
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility GeneralNominalGroundProduction
open GeneralNominalClosedSubstitution GeneralNominalCanonicalTemplates GeneralNominalInspection
open GeneralNominalStructuralContainment
open GeneralNominalHeadMatchMass GeneralNominalTemplateSubstitution
open GeneralPatternNormalForm GeneralPatternVariableProvenance

variable {model : GeneralNominalCommonBridge.Assignment}

theorem normalize_map (patterns : List Pattern) : normalizeArgs patterns = patterns.map normalize := by
  induction patterns <;> simp_all [normalizeArgs]

theorem substitute_map (patterns : List Pattern) (capture : Nat → Pattern) :
    substArgs capture patterns = patterns.map (Pattern.subst capture) := by
  induction patterns <;> simp_all [substArgs]

theorem covered_member (patterns : List Pattern) (known : coveredArgs patterns = true)
    (pattern : Pattern) (member : pattern ∈ patterns) : covered pattern = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
    have parts : covered head = true ∧ coveredArgs tail = true := by simpa only [coveredArgs,Bool.and_eq_true] using known
    rcases List.mem_cons.mp member with rfl | member
    · exact parts.1
    · exact ih parts.2 member

theorem capture_images (packet : Packet roles) (branch : packet.Holds model)
    (generation : GenerationGuard state packet) (ready : Ready context packet model capture) :
    ∃ replacement : Nat → Expr Nat, ∀ name,
      covered (capture name) = true ∧
      translate context.state.constructors context.interpretation (capture name) = quote (replacement name) ∧
      Canonical (replacement name) ∧
      (Needed packet name → (replacement name).leaves = [] ∧
        CaptureValue packet model name (denote (fun _ => .bottom) (replacement name))) := by
  classical
  have each (name : Nat) : ∃ term : Expr Nat,
      covered (capture name) = true ∧
      translate context.state.constructors context.interpretation (capture name) = quote term ∧
      Canonical term ∧ (Needed packet name → term.leaves = [] ∧
        CaptureValue packet model name (denote (fun _ => .bottom) term)) := by
    by_cases needed : Needed packet name
    · obtain ⟨term,closed,meaning⟩ := (ready.2.2 name needed).1
      have translated := closed.1
      rw [ready.1 name] at translated
      have covered := translated_covered (capture name) (by
        rw [translated]; exact GeneralNominalClosedPatternNormal.quote_closed term closed.2.1 closed.2.2)
      obtain ⟨origin,usable⟩ := generation name needed
      exact ⟨term,covered,translated,closed.2.2,fun _ =>
        ⟨closed.2.1,capture_value packet model branch (needed_input packet needed) usable (meaning origin usable)⟩⟩
    · rw [ready.2.1 name needed]
      exact ⟨.leaf name,rfl,by simp only [translate,quote],trivial,fun contrary => False.elim (needed contrary)⟩
  exact ⟨fun name => Classical.choose (each name),fun name => Classical.choose_spec (each name)⟩

theorem child_argument (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (branch : packet.Holds model) (generation : GenerationGuard tracked packet)
    (ready : Ready context packet model capture) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) :
    ∃ term, ClosedTerm context
      ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture) term ∧
      ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term) := by
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
  obtain ⟨replacement,images⟩ := capture_images packet branch generation ready
  by_cases simple : ∃ name, template = .var name
  · obtain ⟨name,equal⟩ := simple
    have needed : Needed packet name := used name (by rw [equal]; exact List.mem_singleton_self _)
    obtain ⟨origin,usable⟩ := generation name needed
    refine ⟨replacement name,?_,Or.inl ⟨name,equal,(images name).2.2.2 needed |>.2,origin,usable⟩⟩
    change ClosedTerm context (template.subst capture) _
    rw [equal]
    exact ⟨by rw [Pattern.subst,ready.1 name]; exact (images name).2.1,
      ((images name).2.2.2 needed).1,(images name).2.2.1⟩
  · have compound : ∀ name, template ≠ .var name := fun name equal => simple ⟨name,equal⟩
    have complete := GeneralNominalRequestCompleteness.input_complete state packet enabled clause present signature index compound
    have complete : Complete (translate context.state.constructors context.interpretation (normalize template)) := by
      simpa only [GeneralNominalCompoundEmission.lowerRequest,constructors,interpretation] using complete
    have normal := normalized template templateCovered
    have variables : Uses (Needed packet) (normalize template) := normalize_uses template used
    obtain ⟨openTerm,translated,canonical,leaves⟩ := quoted _ (translated_good (normalize template) normal complete variables)
    have closed := filled_closed (normalize template) (covered_normal _ normal) complete capture replacement openTerm
      translated.symm canonical (fun name => (images name).1) (fun name => (images name).2.1)
      (fun name member => ((images name).2.2.2 (leaves name member)).1)
      (fun name _ => (images name).2.2.1)
    refine ⟨openTerm.bind replacement,?_,Or.inr ⟨compound,openTerm,
      (fun name => denote (fun _ => .bottom) (replacement name)),canonical,
      (fun name member => ((images name).2.2.2 (leaves name member)).2),?_,?_⟩⟩
    · change ClosedTerm context (template.subst capture) _
      unfold ClosedTerm at closed ⊢
      rw [GeneralPatternRecordSubstitution.normalize_template template templateCovered capture]
      exact closed
    · simpa only [GeneralNominalCompoundEmission.lowerRequest,constructors,interpretation] using translated.symm
    · exact (denote_bind openTerm replacement (fun _ => .bottom)).symm

theorem children (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (branch : packet.Holds model) (generation : GenerationGuard tracked packet)
    (ready : Ready context packet model capture) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles) :
    ∃ length : (substArgs capture (normalizeArgs clause.arguments)).length = (roles clause.role).arity,
      ∀ index : Fin (roles clause.role).arity, ∃ term,
        ClosedTerm context ((substArgs capture (normalizeArgs clause.arguments))[index.val]'(by rw [length]; exact index.isLt)) term ∧
        ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term) := by
  have length : (substArgs capture (normalizeArgs clause.arguments)).length = (roles clause.role).arity := by
    simp only [substitute_map,normalize_map,List.length_map,signature.1]
  refine ⟨length,?_⟩
  intro index
  simpa only [substitute_map,normalize_map,List.getElem_map] using
    child_argument state packet enabled constructors interpretation branch generation ready clause present signature index

end Yulang.GeneralNominalChildAssembly
