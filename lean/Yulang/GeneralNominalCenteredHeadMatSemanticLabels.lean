import Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution

set_option backward.isDefEq.respectTransparency false

/-! Finite semantic labels are normalized patterns, not inspection queries.
They preserve exact and open record tails. Only unnamed where arguments
participate in capture support and the descent inequality. -/
namespace Yulang.GeneralNominalCenteredHeadMatSemanticLabels
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepDepthSupport (frame configuration_trace)
open GeneralNominalPatersonLineage (mass)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}

/-- General finite meanings allow every normalized Pattern, including rows. -/
def Meaning (semantics : Algebra) (value : Ty) (pattern : Pattern) : Prop :=
  (normalize pattern).variables = [] ∧
    Equivalent value (eval semantics (fun _ => .bottom) (normalize pattern))

/-- The declaration check uses this join-free part for unnamed descent. -/
def CountedMeaning (semantics : Algebra) (value : Ty) (pattern : Pattern) : Prop :=
  (normalize pattern).variables = [] ∧ covered (normalize pattern) = true ∧
    Equivalent value (eval semantics (fun _ => .bottom) (normalize pattern))

theorem counted_meaning (known : CountedMeaning semantics value pattern) : Meaning semantics value pattern :=
  ⟨known.1,known.2.2⟩

theorem compiled_meaning
    (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression)
    (closed : (normalize pattern).variables = []) :
    Meaning (algebra catalogue interpretation)
      (GeneralNominalCenteredHeadMatExpressions.value variables .actual expression) pattern := by
  refine ⟨closed,?_⟩
  have first := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized (variables := variables) compiled
  have last : Equivalent (eval (algebra catalogue interpretation) (variables .actual) (normalize pattern))
      (eval (algebra catalogue interpretation) (fun _ => .bottom) (normalize pattern)) := by
    apply eval_congr
    intro name member
    rw [closed] at member
    cases member
  exact eqv_trans first last

theorem compiled_counted_meaning
    (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression)
    (closed : (normalize pattern).variables = []) (counted : covered (normalize pattern) = true) :
    CountedMeaning (algebra catalogue interpretation)
      (GeneralNominalCenteredHeadMatExpressions.value variables .actual expression) pattern :=
  ⟨closed,counted,(compiled_meaning compiled closed).2⟩

def Inputs (semantics : Algebra) (model : Assignment) (site : Site roles) (labels : List Pattern) : Prop :=
  ∃ length : labels.length = (roles site.occurrence.demand.role).arity,
    ∀ index : Fin (roles site.occurrence.demand.role).arity,
      CountedMeaning semantics (model (site.center index)).1 (labels[index.val]'(by rw [length]; exact index.isLt))

def Captures (plan : Plan roles) (model : Assignment) (capture : Nat → Pattern) : Prop :=
  (∀ name, covered (normalize (capture name)) = true) ∧
    ∀ name, GeneralNominalSharedCaptures.Needed plan.packet name →
      CountedMeaning (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
        (model (plan.binder name)).1 (capture name)

def images (capture : Nat → Pattern) (name : Nat) : Pattern := normalize (capture name)

def labels (capture : Nat → Pattern) (clause : Clause) : List Pattern :=
  substArgs (images capture) (normalizeArgs clause.arguments)

theorem needed_unnamed (member : clause ∈ plan.packet.declaration.requirements)
    (used : name ∈ variablesArgs (normalizeArgs clause.arguments)) :
    GeneralNominalSharedCaptures.Needed plan.packet name := ⟨clause,member,used⟩

theorem needed_excludes_output (needed : GeneralNominalSharedCaptures.Needed plan.packet name) :
    name ∉ plan.packet.declaration.outputNames := GeneralPatternVariableProvenance.needed_input plan.packet needed

theorem needed_in_head (needed : GeneralNominalSharedCaptures.Needed plan.packet name) :
    name ∈ plan.packet.declaration.inputNames := by
  obtain ⟨clause,member,used⟩ := needed
  exact plan.packet.checked.scope.1 clause member name used

theorem reachable_patterns_covered
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (current : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (member : clause ∈ plan.packet.declaration.requirements) :
    GeneralNominalCenteredHeadWFSource.PatternsCovered plan.packet.registry.constructors
      plan.packet.context.interpretation clause.arguments := by
  have known := (coverage.1 plan.packet.declaration current.visible).2.1 clause member |>.1
  rw [current.registry_eq,current.context_eq,(configuration_trace path).2.2]
  exact known

theorem argument_needed (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (used : name ∈ (normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).variables) :
    GeneralNominalSharedCaptures.Needed plan.packet name := by
  apply needed_unnamed member
  apply GeneralNominalCanonicalTemplates.argument_variables (normalizeArgs clause.arguments) _ _ used
  rw [GeneralNominalChildAssembly.normalize_map]
  exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩

theorem child_meaning (branch : GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (captures : Captures plan model capture) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (source : GeneralNominalCenteredHeadWFSource.PatternCovered plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) :
    CountedMeaning (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
      (model ((plan.childSite clause signature).center index)).1
      ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst (images capture)) := by
  let pattern := normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))
  have needed : ∀ name ∈ pattern.variables, GeneralNominalSharedCaptures.Needed plan.packet name :=
    fun name used => argument_needed member signature index used
  have complete : covered pattern = true := by
    apply GeneralNominalChildAssembly.covered_member (normalizeArgs clause.arguments)
      (plan.packet.checked.countsCovered clause member).2 pattern
    rw [GeneralNominalChildAssembly.normalize_map]
    exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩
  have closed := subst_closed pattern (images capture) (fun name used => (captures.2 name (needed name used)).1)
  have coveredSubst := GeneralNominalTemplateSubstitution.subst_covered pattern complete (images capture) captures.1
  refine ⟨normalized_closed closed,GeneralPatternNormalForm.covered_normal _
    (GeneralPatternNormalForm.normalized _ coveredSubst),?_⟩
  have before := GeneralNominalCenteredHeadMatCompilerSemantics.child_normalized branch member signature index source
  have substituted := normalized_subst_meaning (images capture)
    (fun name used => (captures.2 name (needed name used)).2.2)
  exact eqv_trans before substituted

theorem child_inputs (branch : GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (captures : Captures plan model capture) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles)
    (source : GeneralNominalCenteredHeadWFSource.PatternsCovered plan.packet.registry.constructors
      plan.packet.context.interpretation clause.arguments) :
    Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model
      (plan.childSite clause signature) (labels capture clause) := by
  have length : (labels capture clause).length = (roles clause.role).arity := by
    simpa only [labels,GeneralNominalChildAssembly.substitute_map,GeneralNominalChildAssembly.normalize_map,
      List.length_map] using signature.1
  refine ⟨length,?_⟩
  intro index
  have meaning := child_meaning branch captures member signature index
    (GeneralNominalCenteredHeadMatSchemas.patterns_member source (List.getElem_mem ..))
  simpa only [labels,GeneralNominalChildAssembly.substitute_map,GeneralNominalChildAssembly.normalize_map,
    List.getElem_map] using meaning

theorem reachable_child_inputs
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (current : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (branch : GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (captures : Captures plan model capture) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) :
    Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model
      (plan.childSite clause signature) (labels capture clause) :=
  child_inputs branch captures member signature (reachable_patterns_covered path coverage current member)

theorem label_descent (checked : DeclarationChecked constructors roles declaration)
    (member : clause ∈ declaration.requirements) (capture : Nat → Pattern) :
    mass (labels capture clause) < mass (substArgs (images capture) (normalizeArgs declaration.head)) :=
  GeneralPatternConservativeSubstitution.checked_normalized_descent checked clause member (images capture)

theorem bounded_label_descent (checked : DeclarationChecked constructors roles declaration)
    (member : clause ∈ declaration.requirements) (capture : Nat → Pattern)
    (headBound : mass (substArgs (images capture) (normalizeArgs declaration.head)) ≤ mass parentLabels) :
    mass (labels capture clause) < mass parentLabels :=
  Nat.lt_of_lt_of_le (label_descent checked member capture) headBound

end Yulang.GeneralNominalCenteredHeadMatSemanticLabels
