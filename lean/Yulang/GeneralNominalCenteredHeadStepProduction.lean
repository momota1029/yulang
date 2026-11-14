import Yulang.GeneralNominalCenteredHeadStepProgress

set_option backward.isDefEq.respectTransparency false

/-! Head preparation and emission completeness suffice for the retrospective
producer. No joint applicability or old installation premise is used. -/
namespace Yulang.GeneralNominalCenteredHeadStepProduction
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatching GeneralNominalCenteredCaptureLabels
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility
open GeneralNominalMaterialization (schema Use)
open GeneralNominalStructuralContainment (included_trans child_included root_test)
open GeneralNominalClosedSubstitution GeneralNominalCanonicalTemplates GeneralNominalHeadMatchMass
open GeneralNominalTemplateSubstitution GeneralPatternVariableProvenance GeneralNominalChildAssembly
open CommonNominalFullCarrier

open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredProduction
open GeneralNominalSaturationState (Packet)
open GeneralNominalInspectionAlignment GeneralNominalInspectionPositions
open GeneralNominalRecursiveInspection GeneralNominalMatchedAssembly GeneralNominalClosedPatternMass

variable {model : GeneralNominalCommonBridge.Assignment}

theorem plan_matching (state : GeneralNominalCenteredHeadStepEffects.State roles) (plan : Plan roles)
    (enabled : Installable registry state plan support)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalCenteredHeadStepEffects.Models state model) (branch : plan.Holds model)
    (known : Inputs context model plan.input.observed labels) :
    HeadMatches context plan model labels := by
  classical
  have sameContext := enabled.frame.context_eq
  have located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds := enabled.frame.located
  have prepared := enabled.frame.prepared
  rw [← sameContext] at prepared
  obtain ⟨_,_,_,bounds,found,headFinished,_⟩ := prepared
  have equal : bounds = plan.packet.bounds := Option.some.inj (found.symm.trans located)
  subst bounds
  have current : GeneralNominalState.Models plan.packet.context.state model := by rw [sameContext]; exact valid.1.1.1
  let origins := fun index : Nat => Origin.source ((List.ofFn plan.input.center)[index]?.getD 0)
  let report := inspectMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
    plan.packet.bounds (fun i => some (origins i)) 0
  have finished : Finished report := finished_origins plan.packet.context.state _ plan.packet.bounds _ _ 0 0
    headFinished
  obtain ⟨clause,present⟩ := List.exists_mem_of_ne_nil _ nonempty
  have covered := (plan.packet.checked.countsCovered clause present).1
  let queries := GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
  have single : ∀ query ∈ queries, Single query := by
    intro query member
    obtain ⟨pattern,present,rfl⟩ := List.mem_map.mp member
    exact translated_single pattern (GeneralNominalChildAssembly.covered_member _ covered pattern present)
  obtain ⟨labelLength,meanings⟩ := known
  change labels.length = (roles plan.input.occurrence.demand.role).arity at labelLength
  let trees : Fin (roles plan.input.occurrence.demand.role).arity → Expr Nat := fun index => Classical.choose (meanings index)
  have treeFacts (index : Fin (roles plan.input.occurrence.demand.role).arity) := Classical.choose_spec (meanings index)
  rw [← plan.input_exact] at located
  have boundsLength : plan.packet.bounds.length = (roles plan.input.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length plan.packet.context.state.base
      (List.ofFn plan.input.occurrence.demand.arguments) plan.packet.bounds located
  have inputTrees : InputsAt context model plan.packet.context.state
      (fun i => some (origins i)) 0 plan.packet.bounds (List.ofFn trees) := by
    apply inputs_at _ _ (by rw [List.length_ofFn,boundsLength])
    intro index
    let position : Fin (roles plan.input.occurrence.demand.role).arity := ⟨index.val,by rw [← boundsLength]; exact index.isLt⟩
    have facts := treeFacts position
    have inside : index.val < (roles plan.input.occurrence.demand.role).arity := position.isLt
    have sources := congrArg (fun inputs => inputs[index.val]?)
      (GeneralNominalPacketCaptureReadback.locate_sources plan.packet.context.state.base
        (List.ofFn plan.input.occurrence.demand.arguments) plan.packet.bounds located)
    have same : (plan.packet.context.state.base.source plan.packet.bounds[index.val].1,plan.packet.context.state.base.source plan.packet.bounds[index.val].2) =
        plan.input.occurrence.demand.arguments position := by
      simpa only [List.getElem?_map,List.getElem?_eq_getElem index.isLt,Option.map_some,List.getElem?_ofFn,
        inside,dite_eq_left,Option.some.injEq] using sources
    simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
    refine ⟨⟨_,facts.1⟩,?_,?_⟩
    · change GeneralNominalCaptureMerges.Fits model _ _
      rw [same]
      exact facts.2.1
    · intro origin retained
      have originEq : origins index.val = origin := Option.some.inj retained
      subst origin
      apply facts.2.2
      simp [Site.observed,origins,inside,position]
  have captureValue : ∀ captured ∈ report.captures, ∀ term,
      Input context model plan.packet.context.state captured.bounds captured.origin term → Part context plan model captured.name term := by
    intro captured member term input
    obtain ⟨origin,recorded,present⟩ := GeneralNominalCenteredCaptureSchema.many_capture
      plan.packet.context.state queries plan.packet.bounds origins 0 captured member
    have shared := branch.2.2.2.1.2 ⟨captured.name,origin,.actual⟩ present
    simp only [ite_true] at shared
    exact ⟨input.1.choose,input.1.choose_spec,
      GeneralNominalSimultaneousCaptures.at_same (input.2.2 origin recorded) shared⟩
  have matched := GeneralNominalRelationalMatching.many_matched plan.packet model current report.captures captureValue
    queries plan.packet.bounds _ 0 (List.ofFn trees) single finished inputTrees (fun _ h => h)
  have queryLength : queries.length = plan.packet.bounds.length := finished_length plan.packet.context.state queries plan.packet.bounds _ 0 finished
  have headLength : (normalizeArgs plan.packet.declaration.head).length = labels.length := by
    have heads : queries.length = (normalizeArgs plan.packet.declaration.head).length := List.length_map ..
    omega
  apply GeneralNominalGroundHeadMatching.aligned_of_positions _ _ headLength
  intro index
  let position : Fin (roles plan.input.occurrence.demand.role).arity := ⟨index.val,by rw [← labelLength,← headLength]; exact index.isLt⟩
  refine ⟨trees position,(treeFacts position).1,?_⟩
  have headQueries : queries.length = (normalizeArgs plan.packet.declaration.head).length := List.length_map ..
  have atIndex := aligned_position matched (by rw [List.length_ofFn,queryLength,boundsLength])
    ⟨index.val,by rw [headQueries]; exact index.isLt⟩
  simpa only [queries,GeneralNominalInspection.queries,Declaration.normalHead,Fin.getElem_fin,
    List.getElem_map,List.getElem_ofFn,constructors,interpretation] using atIndex


theorem child_argument (state : GeneralNominalCenteredHeadStepEffects.State roles) (plan : Plan roles)
    (enabled : Installable registry state plan support)
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
      have prepared := GeneralNominalRequestCompleteness.generated_complete plan.packet.context.state plan.packet.context.interpretation _
        enabled.materialized _ (GeneralNominalRequestCompleteness.input_request_member plan.packet _
          (GeneralNominalCompoundEmission.emitted_requests plan.packet clause present signature index compound).1)
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

theorem child_inputs (state : GeneralNominalCenteredHeadStepEffects.State roles) (plan : Plan roles)
    (enabled : Installable registry state plan support)
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

theorem production (state : GeneralNominalCenteredHeadStepEffects.State roles) (plan : Plan roles)
    (enabled : Installable registry state plan support)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (valid : GeneralNominalCenteredHeadStepEffects.Models state model) (branch : plan.Holds model)
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


end Yulang.GeneralNominalCenteredHeadStepProduction
