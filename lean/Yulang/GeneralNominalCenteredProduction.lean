import Yulang.GeneralNominalCenteredCaptureLabels
import Yulang.GeneralPatternCoveredResult

/-! Prepared centered plans produce finite actual child meanings from finite
input-center meanings. Repeated variables use one minimum-mass label. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredProduction
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatching GeneralNominalCenteredCaptureLabels
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility
open GeneralNominalMaterialization (schema Use)
open GeneralNominalStructuralContainment (included_trans child_included root_test)
open GeneralNominalClosedSubstitution GeneralNominalCanonicalTemplates GeneralNominalHeadMatchMass
open GeneralNominalTemplateSubstitution GeneralPatternVariableProvenance GeneralNominalChildAssembly
open CommonNominalFullCarrier

variable {model : GeneralNominalCommonBridge.Assignment}

theorem schema_value (plan : Plan roles) (valid : plan.SchemaHolds body model)
    (term : Expr Nat) (canonical : Canonical term) (values : Nat → Ty)
    (captures : ∀ name ∈ term.leaves, At model .actual (.source (plan.binder name)) (values name))
    (root : GeneralNominalRecursiveInspection.Origin) (unique : Unique model root)
    (included : Included (schema (quote term) root .actual) body) :
    At model .actual root (denote values term) := by
  induction term generalizing root with
  | leaf name =>
    have member : (⟨name,root,.actual⟩ : Use) ∈ body.variables := included.2 (by simp [quote,schema])
    have shared := valid.2 _ member
    simp only [ite_true] at shared
    exact GeneralNominalSimultaneousCaptures.at_same (captures name (by simp [Expr.leaves])) (same_symm shared)
  | node test children ih =>
    apply assemble test .actual (fun index => denote values (children index)) unique
      (valid.1 _ (included.1 (root_test test children root .actual)))
    intro index
    have actual : childMode test .actual = .actual := by cases test <;> rfl
    rw [actual]
    refine ih index (canonical.2 index) ?_ _ (projection_unique unique test canonical.1 index) ?_
    · intro name member
      apply captures name
      simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
      exact ⟨_,⟨index,rfl⟩,member⟩
    · apply included_trans _ included
      simpa only [actual] using child_included test children root .actual index

theorem capture_images (ready : Ready context plan model capture) :
    ∃ replacement : Nat → Expr Nat, ∀ name,
      covered (capture name) = true ∧
      GeneralNominalInspection.translate context.state.constructors context.interpretation (capture name) = quote (replacement name) ∧
      Canonical (replacement name) ∧
      (GeneralNominalSharedCaptures.Needed plan.packet name → (replacement name).leaves = [] ∧
        At model .actual (.source (plan.binder name)) (denote (fun _ => .bottom) (replacement name))) := by
  classical
  have each (name : Nat) : ∃ term : Expr Nat,
      covered (capture name) = true ∧
      GeneralNominalInspection.translate context.state.constructors context.interpretation (capture name) = quote term ∧
      Canonical term ∧ (GeneralNominalSharedCaptures.Needed plan.packet name → term.leaves = [] ∧
        At model .actual (.source (plan.binder name)) (denote (fun _ => .bottom) term)) := by
    by_cases needed : GeneralNominalSharedCaptures.Needed plan.packet name
    · obtain ⟨term,closed,meaning⟩ := (ready.2.2 name needed).1
      have translated := closed.1
      rw [ready.1 name] at translated
      have covered := translated_covered (capture name) (by
        rw [translated]; exact GeneralNominalClosedPatternNormal.quote_closed term closed.2.1 closed.2.2)
      exact ⟨term,covered,translated,closed.2.2,fun _ => ⟨closed.2.1,meaning⟩⟩
    · rw [ready.2.1 name needed]
      exact ⟨.leaf name,rfl,by simp only [GeneralNominalInspection.translate,quote],trivial,
        fun contrary => False.elim (needed contrary)⟩
  exact ⟨fun name => Classical.choose (each name),fun name => Classical.choose_spec (each name)⟩

theorem child_argument (state : GeneralNominalSaturationState.State roles) (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (branch : plan.Holds model) (ready : Ready context plan model capture)
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) :
    ∃ term, ClosedTerm context
      ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture) term ∧
      At model .actual (.source ((plan.childSite clause signature).center index)) (denote (fun _ => .bottom) term) := by
  classical
  let raw := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
  let template := normalize raw
  have templateMember : template ∈ normalizeArgs clause.arguments := by
    rw [normalize_map]
    exact List.mem_map.mpr ⟨raw,List.getElem_mem ..,rfl⟩
  have templateCovered : covered template = true := covered_member _
    (plan.packet.checked.countsCovered clause present).2 template templateMember
  have normal := GeneralPatternCoveredResult.covered_result_normal raw templateCovered
  have fixed : normalize template = template := GeneralPatternNormalForm.fixed template normal
  have used : Uses (GeneralNominalSharedCaptures.Needed plan.packet) template := fun name member =>
    ⟨clause,present,argument_variables _ template templateMember member⟩
  have complete : Complete (GeneralNominalInspection.translate context.state.constructors context.interpretation template) := by
    by_cases simple : ∃ name, template = .var name
    · obtain ⟨name,same⟩ := simple
      rw [same]
      simp only [GeneralNominalInspection.translate,Complete]
    · have compound : ∀ name, template ≠ .var name := fun name same => simple ⟨name,same⟩
      have prepared := GeneralNominalRequestCompleteness.input_complete state plan.packet enabled clause present signature index compound
      change Complete (GeneralNominalInspection.translate plan.packet.context.state.constructors
        plan.packet.context.interpretation (normalize template)) at prepared
      simpa only [constructors,interpretation,fixed] using prepared
  obtain ⟨replacement,images⟩ := capture_images ready
  obtain ⟨openTerm,translated,canonical,leaves⟩ := quoted _ (translated_good template normal complete used)
  have closed := filled_closed template templateCovered complete capture replacement openTerm translated.symm canonical
    (fun name => (images name).1) (fun name => (images name).2.1)
    (fun name member => ((images name).2.2.2 (leaves name member)).1)
    (fun name _ => (images name).2.2.1)
  refine ⟨openTerm.bind replacement,closed,?_⟩
  rw [denote_bind]
  apply schema_value plan (branch.2.2.2.2.2.2 clause present signature).2 openTerm canonical
    (fun name => denote (fun _ => .bottom) (replacement name))
    (fun name member => ((images name).2.2.2 (leaves name member)).2) _ (source_unique model _) 
  have requested : (⟨raw,(plan.childSite clause signature).center index,.actual⟩ : GeneralNominalMaterialization.Request) ∈
      plan.childRequests clause signature := List.mem_ofFn.mpr ⟨index,rfl⟩
  have included := request_included plan.packet.context.state plan.packet.context.interpretation
    (plan.childRequests clause signature) _ requested
  have query : GeneralNominalInspection.translate plan.packet.context.state.constructors
      plan.packet.context.interpretation (normalize raw) = quote openTerm := by
    rw [constructors,interpretation]
    exact translated.symm
  change Included (schema (GeneralNominalInspection.translate plan.packet.context.state.constructors
    plan.packet.context.interpretation (normalize raw)) _ .actual) (plan.schema _) at included
  rw [query] at included
  exact included

theorem child_inputs (state : GeneralNominalSaturationState.State roles) (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (branch : plan.Holds model) (ready : Ready context plan model capture)
    (clause : Clause) (present : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
    Inputs context model (plan.childSite clause signature).observed (substArgs capture (normalizeArgs clause.arguments)) := by
  have length : (substArgs capture (normalizeArgs clause.arguments)).length = (roles clause.role).arity := by
    simp only [substitute_map,normalize_map,List.length_map,signature.1]
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,meaning⟩ := child_argument state plan enabled constructors interpretation branch ready clause present signature index
  refine ⟨term,?_,?_,?_⟩
  · simpa only [substitute_map,normalize_map,List.getElem_map] using closed
  · have fit := (branch.2.2.2.2.2.2 clause present signature).1 index
    have equal := meaning.2 _ (.source _)
    exact ⟨subtype_trans fit.1 equal.1,subtype_trans equal.2 fit.2⟩
  · intro origin recorded
    have same : .source ((plan.childSite clause signature).center index) = origin := by
      change (List.ofFn (fun i : Fin (roles clause.role).arity =>
        some (GeneralNominalRecursiveInspection.Origin.source ((plan.childSite clause signature).center i))))[index.val]? =
        some (some origin) at recorded
      rw [List.getElem?_ofFn] at recorded
      split at recorded
      · rename_i inside
        have equal : (⟨index.val,inside⟩ : Fin (roles clause.role).arity) = index := Fin.ext rfl
        simpa only [equal,Option.some.injEq] using recorded
      · exact False.elim (‹¬ _› index.isLt)
    exact same ▸ meaning

theorem production (state : GeneralNominalSaturationState.State roles) (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (valid : GeneralNominalSaturationState.Models state model) (branch : plan.Holds model)
    (known : Inputs context model plan.input.observed labels) :
    ∃ capture, GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs plan.packet.declaration.head)) ≤
        GeneralNominalPatersonLineage.mass labels ∧
      ∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
        Inputs context model (plan.childSite clause signature).observed (substArgs capture (normalizeArgs clause.arguments)) := by
  have matched := plan_matching state plan enabled constructors interpretation nonempty model valid branch known
  obtain ⟨capture,ready⟩ := ready_captures matched nonempty
  refine ⟨capture,?_,fun clause present signature => child_inputs state plan enabled constructors interpretation branch ready clause present signature⟩
  obtain ⟨clause,present⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact list_mass matched (plan.packet.checked.countsCovered clause present).1 ready

end Yulang.GeneralNominalCenteredProduction
