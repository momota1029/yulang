import Yulang.GeneralNominalCenteredSourceInvariant

/-! Actual centered child schemas compose finite binder values into the exact
substituted source syntax. The capture substitution is shared by every child;
this construction makes no model-dependent choice of a child tree. -/
namespace Yulang.GeneralNominalCenteredChildSourceValues
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalMaterialization GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalOpenPatternLabels GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalSourceLabelVocabulary
open GeneralNominalSharedCaptures (Needed)
open GeneralNominalCenteredSourceInvariant (keyMenu testMenu)

variable {roles : Roles.RoleDecls} {plan : Plan roles}
variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {origins : Nat → Origin} {remaining keys : List Nat} {tests : List Test}

mutual
  theorem covered_tidy (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (tidy : GeneralNominalRequestCanonical.Tidy pattern) : GeneralPatternNormalForm.Normal pattern := by
    cases pattern with
    | var => simp only [GeneralPatternNormalForm.Normal]
    | app key arguments =>
      simp only [GeneralNominalRequestCanonical.Tidy,GeneralPatternNormalForm.Normal] at tidy ⊢
      exact covered_args_tidy arguments covered tidy
    | variant tag payload =>
      simp only [GeneralNominalRequestCanonical.Tidy,GeneralPatternNormalForm.Normal] at tidy ⊢
      exact covered_tidy payload covered tidy
    | join => cases covered
    | record label payload tail =>
      simp only [GeneralNominalRequestCanonical.Tidy,GeneralPatternNormalForm.Normal] at tidy ⊢
      have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true :=
        (Bool.and_eq_true ..).mp covered
      exact ⟨covered_tidy payload parts.1 tidy.1,covered_tidy tail parts.2 tidy.2.1,tidy.2.2⟩
  theorem covered_args_tidy (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (tidy : ∀ pattern ∈ patterns, GeneralNominalRequestCanonical.Tidy pattern) :
      ∀ pattern ∈ patterns, GeneralPatternNormalForm.Normal pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons first rest =>
      have parts : GeneralDeclarationPatterns.covered first = true ∧ coveredArgs rest = true :=
        (Bool.and_eq_true ..).mp covered
      intro pattern member
      rcases List.mem_cons.mp member with equal | member
      · exact equal.symm ▸ covered_tidy first parts.1 (tidy first (List.mem_cons_self ..))
      · exact covered_args_tidy rest parts.2
          (fun pattern member => tidy pattern (List.mem_cons_of_mem _ member)) pattern member
end

theorem recipe_readback (recipe : Recipe body root term)
    (known : ∀ model, models model → plan.SchemaHolds body model)
    (replacement : Nat → Expr Nat)
    (binders : ∀ name ∈ term.leaves,
      Readback models origins remaining (.source (plan.binder name)) (replacement name)) :
    Readback models origins remaining root (term.bind replacement) := by
  induction recipe with
  | capture origin name member =>
    apply alias (binders name (List.mem_singleton_self _))
    intro model valid
    have same := (known model valid).2 _ member
    exact same_symm same
  | node origin test children member recipes ih =>
    have each (position) := ih position (fun name present => binders name
      (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨position,rfl⟩,present⟩))
    constructor
    · intro model valid
      exact ⟨(known model valid).1 _ member,fun position => (each position).1 model valid⟩
    · intro hole present
      obtain ⟨part,partMember,present⟩ := List.mem_flatten.mp present
      obtain ⟨position,rfl⟩ := List.mem_ofFn.mp partMember
      exact (each position).2 hole present

theorem filled_value (recipe : Recipe body root term)
    (known : ∀ model, models model → plan.SchemaHolds body model)
    (label : Label context pattern term) (scope : Scoped keys pattern)
    (used : GeneralPatternVariableProvenance.Uses needed pattern)
    (leaves : ∀ name ∈ term.leaves, needed name)
    (capture : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (scopes : ∀ name, Scoped keys (capture name))
    (represented : ∀ name, needed name →
      Readback models origins remaining (.source (plan.binder name)) (replacement name) ∧
      GeneralPatternVariableProvenance.Uses (fun hole => hole ∈ remaining) (capture name) ∧
      Vocabulary tests (replacement name))
    (vocabulary : Vocabulary tests term) :
    ∃ value : Value models context origins remaining keys root,
      value.pattern = normalize (pattern.subst capture) ∧
      value.term = term.bind replacement ∧ Vocabulary tests value.term := by
  have readback := recipe_readback recipe known replacement
    (fun name member => (represented name (leaves name member)).1)
  refine ⟨⟨normalize (pattern.subst capture),term.bind replacement,
    ⟨filled_label label capture replacement images,readback⟩,?_,?_⟩,rfl,rfl,?_⟩
  · exact normalized_subst_scoped label.1 scope capture scopes (fun name => (images name).1)
  · exact GeneralPatternVariableProvenance.normalize_uses _
      (subst_uses pattern used (fun name needed => (represented name needed).2.1))
  · exact vocabulary_bind vocabulary (fun name member => (represented name (leaves name member)).2.2)

theorem child_template (state : GeneralNominalSaturationState.State roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity) :
    ∃ term, Label context
      (normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) term ∧
      ∀ name ∈ term.leaves, Needed plan.packet name := by
  let raw := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
  let template := normalize raw
  have member : template ∈ normalizeArgs clause.arguments := by
    rw [GeneralNominalChildAssembly.normalize_map]
    exact List.mem_map.mpr ⟨raw,List.getElem_mem ..,rfl⟩
  have covered := GeneralNominalChildAssembly.covered_member _
    (plan.packet.checked.countsCovered clause present).2 template member
  have used : GeneralPatternVariableProvenance.Uses (Needed plan.packet) template :=
    fun name used => ⟨clause,present,GeneralNominalCanonicalTemplates.argument_variables _ template member used⟩
  by_cases simple : ∃ name, template = .var name
  · obtain ⟨name,equal⟩ := simple
    refine ⟨.leaf name,?_,?_⟩
    · change Label context template _
      rw [equal]
      exact ⟨rfl,by simp only [GeneralNominalInspection.translate,quote],True.intro⟩
    · intro actual member
      cases List.mem_singleton.mp member
      exact used name (by rw [equal]; exact List.mem_singleton_self _)
  · have complete := GeneralNominalRequestCompleteness.input_complete state plan.packet enabled clause present signature index
      (fun name equal => simple ⟨name,equal⟩)
    have complete : GeneralNominalHeadMatchMass.Complete
        (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize template)) := by
      simpa only [GeneralNominalCompoundEmission.lowerRequest,constructors,interpretation] using complete
    obtain ⟨term,translated,canonical,leaves⟩ := GeneralNominalCanonicalTemplates.quoted _
      (GeneralNominalCanonicalTemplates.translated_good (normalize template)
        (GeneralPatternNormalForm.normalized template covered) complete
        (GeneralPatternVariableProvenance.normalize_uses _ used))
    have label : Label context (normalize template) term :=
      ⟨GeneralPatternNormalForm.covered_normal _ (GeneralPatternNormalForm.normalized template covered),translated.symm,canonical⟩
    have idempotent : normalize template = template := by
      exact GeneralPatternNormalForm.fixed template
        (covered_tidy template covered (GeneralNominalRequestCanonical.normalized_tidy raw))
    exact ⟨term,by simpa only [idempotent] using label,leaves⟩

theorem child_recipe (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation
      (normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) = quote term) :
    Recipe (plan.schema (plan.childRequests clause signature))
      (.source ((plan.childSite clause signature).center index)) term := by
  let request : Request := ⟨clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt),
    (plan.childSite clause signature).center index,.actual⟩
  have member : request ∈ plan.childRequests clause signature := List.mem_ofFn.mpr ⟨index,rfl⟩
  have included := request_included plan.packet.context.state plan.packet.context.interpretation
    (plan.childRequests clause signature) request member
  change Included (schema _ _ .actual) _ at included
  change GeneralNominalInspection.translate _ _ (normalize request.pattern) = quote term at translated
  rw [translated] at included
  exact recipe_mono (quote_recipe term _) included

theorem child_value (state : GeneralNominalSaturationState.State roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (known : ∀ model, models model → GeneralNominalCenteredSupport.Inputs plan model)
    (capture : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (scopes : ∀ name, Scoped (keyMenu registry) (capture name))
    (represented : ∀ name, Needed plan.packet name →
      Readback models origins remaining (.source (plan.binder name)) (replacement name) ∧
      GeneralPatternVariableProvenance.Uses (fun hole => hole ∈ remaining) (capture name) ∧
      Vocabulary (testMenu context registry) (replacement name))
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity) :
    ∃ value : Value models context origins remaining (keyMenu registry)
      (.source ((plan.childSite clause signature).center index)),
      value.pattern = normalize ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture) ∧
      Vocabulary (testMenu context registry) value.term := by
  obtain ⟨term,label,leaves⟩ := child_template state enabled constructors interpretation clause present signature index
  let template := normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))
  have fixed : normalize template = template := label_normal label
  have member : template ∈ GeneralNominalSchemaBudget.menu plan.packet.declaration :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨clause,present,List.mem_append_left _
      (List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩)⟩)
  have scope : Scoped (keyMenu registry) template := by
    have result := GeneralNominalCenteredSourceInvariant.source_scoped enabled.1.2.2.2.1
      (List.mem_append_right _ member)
    rw [fixed] at result
    exact result
  have used : GeneralPatternVariableProvenance.Uses (Needed plan.packet) template := by
    intro name used
    refine ⟨clause,present,GeneralNominalCanonicalTemplates.argument_variables _ template ?_ used⟩
    rw [GeneralNominalChildAssembly.normalize_map]
    exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩
  have vocabulary : Vocabulary (testMenu context registry) term := by
    apply GeneralNominalScopedRecipeLabels.recipe_vocabulary (quote_recipe term (.source 0))
    intro entry present
    apply List.mem_flatMap.mpr
    refine ⟨plan.packet.declaration,enabled.1.2.2.2.1,List.mem_flatMap.mpr
      ⟨template,List.mem_append_right _ member,?_⟩⟩
    rw [fixed,label.2.1,← GeneralNominalSchemaVocabulary.schema_vocabulary (quote term) (.source 0) .actual]
    exact List.mem_map.mpr ⟨entry,present,rfl⟩
  have translated : GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation template = quote term := by
    rw [constructors,interpretation]
    exact label.2.1
  obtain ⟨value,equal,_,vocab⟩ := filled_value (child_recipe clause signature index translated)
    (fun model valid => ((known model valid).2.2.2.2.2 clause present signature).2)
    label scope used leaves capture replacement images scopes represented vocabulary
  exact ⟨value,equal,vocab⟩

theorem child_site (state : GeneralNominalSaturationState.State roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (known : ∀ model, models model → GeneralNominalCenteredSupport.Inputs plan model)
    (capture : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (scopes : ∀ name, Scoped (keyMenu registry) (capture name))
    (represented : ∀ name, Needed plan.packet name →
      Readback models (GeneralNominalCenteredSourceInvariant.origins context) remaining
        (.source (plan.binder name)) (replacement name) ∧
      GeneralPatternVariableProvenance.Uses (fun hole => hole ∈ remaining) (capture name) ∧
      Vocabulary (testMenu context registry) (replacement name))
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles)
    (labels : Occurrence roles → List Pattern)
    (equal : labels (plan.childSite clause signature).occurrence =
      normalizeArgs (substArgs capture (normalizeArgs clause.arguments))) :
    GeneralNominalCenteredSourceInvariant.SiteValues models context remaining (keyMenu registry)
      (testMenu context registry) labels (plan.childSite clause signature) := by
  classical
  have each := fun index => child_value state enabled constructors interpretation known capture replacement
    images scopes represented clause present signature index
  let values := fun index => Classical.choose (each index)
  have selected := fun index => Classical.choose_spec (each index)
  refine ⟨values,?_,fun index => (selected index).2⟩
  rw [equal]
  apply List.ext_getElem
  · simp only [GeneralNominalChildAssembly.normalize_map,GeneralNominalChildAssembly.substitute_map,
      List.length_map,List.length_ofFn,signature.1]
    rfl
  · intro index left right
    simp only [GeneralNominalChildAssembly.normalize_map,GeneralNominalChildAssembly.substitute_map,
      List.getElem_map,List.getElem_ofFn]
    have small : index < (roles clause.role).arity := by
      simpa only [GeneralNominalChildAssembly.normalize_map,GeneralNominalChildAssembly.substitute_map,
        List.length_map,signature.1] using left
    exact (selected ⟨index,small⟩).1.symm

end Yulang.GeneralNominalCenteredChildSourceValues
