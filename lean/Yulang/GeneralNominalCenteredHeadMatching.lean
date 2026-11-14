import Yulang.GeneralNominalCenteredCaptureSchema

/-! Actual center meanings instantiate relation-parametric head matching.
No retained raw capture or source identity for a nested position is required. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredHeadMatching
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalCenters
open GeneralNominalGroundAccessibility GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalRecursiveInspection GeneralNominalMatchedAssembly GeneralNominalHeadMatchMass
open GeneralNominalInspectionAlignment GeneralNominalInspectionPositions
open GeneralNominalClosedPatternMass

def Part (context : GeneralNominalCandidates.Context) (plan : Plan roles)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (term : Expr Nat) : Prop :=
  ∃ pattern, ClosedTerm context pattern term ∧
    At model .actual (.source (plan.binder name)) (denote (fun _ => .bottom) term)

def HeadMatches (context : GeneralNominalCandidates.Context) (plan : Plan roles)
    (model : GeneralNominalCommonBridge.Assignment) (labels : List Pattern) : Prop :=
  Aligned (fun pattern label => ∃ term, ClosedTerm context label term ∧
    Matches (Part context plan model)
      (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
    (normalizeArgs plan.packet.declaration.head) labels

theorem plan_matching (state : GeneralNominalSaturationState.State roles) (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state plan.packet)
    (constructors : plan.packet.context.state.constructors = context.state.constructors)
    (interpretation : plan.packet.context.interpretation = context.interpretation)
    (nonempty : plan.packet.declaration.requirements ≠ [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) (branch : plan.Holds model)
    (known : Inputs context model plan.input.observed labels) :
    HeadMatches context plan model labels := by
  classical
  obtain ⟨_,sameContext,_,_,_,located,prepared,_,_,_,_,_⟩ := enabled.1
  have current : GeneralNominalState.Models plan.packet.context.state model := by rw [sameContext]; exact valid.1
  let origins := fun index : Nat => Origin.source ((List.ofFn plan.input.center)[index]?.getD 0)
  let report := inspectMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
    plan.packet.bounds (fun i => some (origins i)) 0
  have finished : Finished report := finished_origins plan.packet.context.state _ plan.packet.bounds _ _ 0 0
    (GeneralNominalGroundHeadMatching.prepared_finished plan.packet prepared located)
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

end Yulang.GeneralNominalCenteredHeadMatching
