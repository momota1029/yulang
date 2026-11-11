import Yulang.GeneralCandidateBoundaryParts
import Yulang.GeneralDeclarationExamples
import Yulang.GeneralSourceK2Examples
import Yulang.CommonRigidHeadInspection

/-!
# Candidate regressions on the shared general carriers

The record fixtures exercise normalized inspection, deferred descendants,
private ordinary propagation, and candidate K2. The nominal examples retain
their actual list applications and expose the missing interpretation instead
of giving list an unrelated ordinary encoding.
-/
namespace Yulang.GeneralCandidateExamples

open GeneralSourceState (State Assignment Models equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (All Atom)
open GeneralCandidateInspection
open GeneralCandidateBoundaryParts
open GeneralDeclarationPatterns
open GeneralDeclarations

private theorem two_cases (slot : Fin 2) : slot = 0 ∨ slot = 1 := by
  by_cases zero : slot.val = 0
  · exact Or.inl (Fin.ext zero)
  · exact Or.inr (Fin.ext (by omega))

abbrev roles := GeneralDeclarationExamples.roles
abbrev constructors := GeneralDeclarationExamples.constructors
abbrev primitives : Primitives := fun name => if name = 4 then some .emptyRecord else none

private theorem primitives_compatible : PrimitivesCompatible constructors primitives := by
  intro name primitive observed
  by_cases four : name = 4
  · subst name
    have same : Primitive.emptyRecord = primitive := by simpa [primitives] using observed
    subst primitive
    exact ⟨⟨[], 4⟩, rfl, rfl⟩
  · simp [primitives, four] at observed

abbrev recordShapes : Fin 2 → GeneralSourceState.Shape 2 :=
  fun kind => .required (if kind = 0 then 8 else 7)
abbrev recordHeads (resolved : Bool) : Fin 2 → GeneralSourceState.Head recordShapes :=
  fun slot => if slot = 0 then .structural 0 (fun _ => 1)
    else if resolved then .structural 1 (fun _ => 1) else .unresolved

abbrev recordState (resolved : Bool) : State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.required 8 (.var 1)) ++
    if resolved then equationAtoms 1 (.required 7 (.var 1)) else []
  kinds := 2
  shapes := recordShapes
  shapes_injective := by
    intro first last same
    rcases two_cases first with rfl | rfl <;> rcases two_cases last with rfl | rfl <;>
      simp_all [recordShapes]
  heads := recordHeads resolved
  intervals := [(0, 0), (1, 1)]
  heads_sound := by
    intro assignment valid slot term recorded
    have both := (PresenceNormalForm.all_append ..).mp valid
    rcases two_cases slot with rfl | rfl
    · have equal : (.required 8 (.var 1) : TyTerm (Fin 2)) = term := by
        simpa [recordHeads, GeneralSourceState.Head.equation, recordShapes,
          GeneralSourceState.Shape.term] using recorded
      subst term
      exact (equationAtoms_exact ..).mp both.1
    · cases resolved with
      | false => simp [recordHeads, GeneralSourceState.Head.equation] at recorded
      | true =>
          have equal : (.required 7 (.var 1) : TyTerm (Fin 2)) = term := by
            simpa [recordHeads, GeneralSourceState.Head.equation, recordShapes,
              GeneralSourceState.Shape.term] using recorded
          subst term
          exact (equationAtoms_exact ..).mp both.2
  intervals_sound := by
    intro assignment _ pair member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _

abbrev recordView (resolved : Bool) : GeneralNormalizedObservation.Snapshot (recordState resolved) where
  kinds := 2
  shapes := fun kind => .record [if kind = 0 then 8 else 7]
  shapes_injective := by
    intro first last same
    rcases two_cases first with rfl | rfl <;> rcases two_cases last with rfl | rfl <;> simp_all
  canonical := by intro kind; simp [GeneralNormalizedObservation.Shape.Canonical]
  heads := fun slot => if slot = 0 then .structural 0 (fun _ => 1)
    else if resolved then .structural 1 (fun _ => 1) else .deferred .unresolved
  checked := by
    intro slot term recorded
    rcases two_cases slot with rfl | rfl
    · have equal : (.record 8 (.var 1) .emptyRecord : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term, GeneralNormalizedObservation.Shape.term,
          GeneralNormalizedObservation.recordTerm, List.ofFn_succ] using recorded
      subst term
      exact .trans (.head rfl) .required
    · cases resolved with
      | false => simp [GeneralNormalizedObservation.Head.term, GeneralNormalizedObservation.Deferred.term] at recorded
      | true =>
          have equal : (.record 7 (.var 1) .emptyRecord : TyTerm (Fin 2)) = term := by
            simpa [GeneralNormalizedObservation.Head.term, GeneralNormalizedObservation.Shape.term,
              GeneralNormalizedObservation.recordTerm, List.ofFn_succ] using recorded
          subst term
          exact .trans (.head rfl) .required

abbrev frame : GeneralDictionaryEmissionPlans.Frame roles where
  capture := fun _ => ⟨fun _ => (1, 1), fun _ => 1⟩
  allocation := fun _ _ => ⟨fun _ => (1, 1), fun _ => 1⟩
  identity := fun invocation declaration clause => invocation + declaration + clause

abbrev context (resolved : Bool) : Context roles :=
  ⟨recordState resolved, primitives, recordView resolved, fun _ => frame, fun _ _ _ => (1, 1)⟩

abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨100, ⟨0, fun _ => (0, 0), [], by intro output member; cases member⟩⟩

abbrev recursiveHead : Declaration :=
  ⟨40, 0, [.record 8 (.record 7 (.var 0) (.app 4 [])) (.app 4 [])], [], [], []⟩

theorem recursive_head_checked : DeclarationChecked constructors roles recursiveHead := by
  constructor
  · simp [Declaration.Signature, roles, GeneralDeclarationExamples.roles, GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  all_goals intro clause member; cases member

abbrev registry : Registry := ⟨constructors, roles, [recursiveHead]⟩

private theorem root_linked (resolved : Bool) : GeneralSourceState.Linked (recordState resolved) root.demand := by
  constructor
  · intro argument; exact ⟨(0, 0), by simp [recordState], rfl⟩
  · intro output member; cases member

private theorem root_ready (resolved : Bool) : ¬ RootPending (context resolved) root := by
  rintro ⟨argument, _, unknown⟩
  exact unknown ⟨0, rfl, by simp [GeneralNormalizedObservation.Snapshot.graph,
    GeneralNormalizedObservation.Head.node]⟩

theorem root_arguments (resolved : Bool) : arguments (context resolved) root = some [(0, 0)] := by
  cases resolved <;> decide +kernel

theorem translated_record : headQueries primitives recursiveHead =
    [.node (.record [8]) [.node (.record [7]) [.variables [0]]]] := by
  simp [headQueries, Declaration.normalHead, normalizeArgs, normalize, hide, translate, primitives]

theorem recursive_captures :
    (report (context true) root recursiveHead [(0, 0)]).captures = [(0, (1, 1))] := by
  simp only [report, translated_record]
  repeat first
    | rw [inspectMany.eq_2]
    | rw [inspectMany.eq_1]
    | rw [inspect.eq_4]
    | rw [inspect.eq_1]
    | simp [Report.visit, Report.append, GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]

private theorem record_covered (resolved : Bool) : GeneralCandidateIntervals.Covered (recordState resolved) := by
  constructor
  · cases resolved <;>
      simp [PresenceGeneratedChildGrammar.GoodAtoms, PresenceGeneratedChildGrammar.GoodAtom,
        PresenceGeneratedChildGrammar.lower, PresenceGeneratedChildGrammar.upper, recordState, equationAtoms]
  · intro source target member tail needed
    cases resolved
    · simp [recordState, equationAtoms] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases needed
    · simp [recordState, equationAtoms] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases needed

  · cases resolved <;>
      simp [PresenceSourceConstraintSupport.GoodAtoms, PresenceSourceConstraintSupport.GoodAtom,
        PresenceSourceConstraintSupport.simpleTyRows, recordState, equationAtoms]
  · exact fun _ _ equal => Fin.ext equal

abbrev recordSource : CommonRoleRecordGraphBridge.RecordGraph 2 :=
  fun slot => (if slot = 0 then 8 else 7, 1)
abbrev recordModel : Assignment := fun source =>
  (CommonRoleRecordGraphBridge.common recordSource (if source = 0 then 0 else 1), Common.rowEmpty)

theorem recursive_state_model : Models (recordState true) recordModel := by
  apply (GeneralSourceState.models_ordinary ..).mpr
  apply (PresenceNormalForm.all_append ..).mpr
  constructor
  · exact (equationAtoms_exact ..).mpr (CommonRoleRecordGraphBridge.common_unfold recordSource 0)
  · exact (equationAtoms_exact ..).mpr (CommonRoleRecordGraphBridge.common_unfold recordSource 1)

theorem recursive_private_model :
    Models (GeneralCandidateIntervals.propagate (recordState true)
      (report (context true) root recursiveHead [(0, 0)]).captures) recordModel := by
  apply (GeneralCandidateIntervals.propagate_models ..).mpr
  refine ⟨recursive_state_model, ?_⟩
  rw [recursive_captures]
  intro name named first firstMember last lastMember
  simp [CommonRoleCandidateConstraints.names] at named
  subst name
  simp [CommonRoleCandidateConstraints.bounds] at firstMember lastMember
  subst first; subst last
  exact Common.subtype_refl _

theorem recursive_head_ready : HeadReady (context true) root recursiveHead := by
  refine ⟨[(0, 0)], root_arguments true, ?_, ?_⟩
  · simp only [Finished, report, translated_record]
    repeat first
      | rw [inspectMany.eq_2]
      | rw [inspectMany.eq_1]
      | rw [inspect.eq_4]
      | rw [inspect.eq_1]
      | simp [Report.visit, Report.append, GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]
  · exact GeneralCandidateIntervals.model_survives _ _ (record_covered true) recordModel recursive_private_model

theorem recursive_inspection_K2 : NeedsK2 (recordView true)
    (report (context true) root recursiveHead [(0, 0)]) := by
  refine ⟨⟨.node (.record [7]) [.variables [0]], (1, 1)⟩, ?_, ?_, ?_⟩
  · simp only [report, translated_record]
    repeat first
      | rw [inspectMany.eq_2]
      | rw [inspectMany.eq_1]
      | rw [inspect.eq_4]
      | rw [inspect.eq_1]
      | simp [Report.visit, Report.append, GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]
  · intro slot _
    rcases two_cases slot with rfl | rfl <;>
      simp [GeneralNormalizedObservation.Snapshot.graph, GeneralNormalizedObservation.Head.node]
  · apply Or.inl
    refine ⟨1, [1], ?_, 1, by simp, .nil _⟩
    simp [GeneralNormalizedObservation.Snapshot.graph, GeneralNormalizedObservation.Head.node,
      GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]

theorem candidate_K2_example : CandidateK2 registry (context true) root := by
  exact ⟨root_ready true, recursiveHead, by simp, recursive_head_checked, rfl,
    recursive_head_ready, rfl, root_linked true, [(0, 0)], root_arguments true, recursive_inspection_K2, primitives_compatible⟩

theorem reached_constructor_not_root : ¬ RootK2 (context true) root := by
  rintro ⟨_, _, argument, slot, source, _, recursive⟩
  have zero : slot = 0 := Fin.ext source
  subst slot
  have absent : CommonRoleGraphBisimulation.regularAt (recordView true).graph 0 = false := by decide +kernel
  have present := (CommonRoleGraphBisimulation.regular_at_exact (recordView true).graph 0).mpr recursive
  rw [absent] at present
  cases present

theorem descendant_inspection_deferred :
    (report (context false) root recursiveHead [(0, 0)]).blocked ≠ [] := by
  simp only [report, translated_record]
  repeat first
    | rw [inspectMany.eq_2]
    | rw [inspectMany.eq_1]
    | rw [inspect.eq_4]
    | rw [inspect.eq_1]
    | simp [Report.visit, Report.append, blocked, GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]

private theorem unfinished_report :
    (report (context false) root recursiveHead [(0, 0)]).captures = [] ∧
      (report (context false) root recursiveHead [(0, 0)]).conflicts = [] := by
  simp only [report, translated_record]
  repeat first
    | rw [inspectMany.eq_2]
    | rw [inspectMany.eq_1]
    | rw [inspect.eq_4]
    | simp [Report.visit, Report.append, blocked, GeneralNormalizedObservation.Shape.arity, List.ofFn_succ]

private theorem unfinished_model : Models (recordState false) recordModel := by
  apply (GeneralSourceState.models_ordinary ..).mpr
  change All Common.model ((recordState false).assignment recordModel)
    (equationAtoms 0 (.required 8 (.var 1)) ++ [])
  rw [List.append_nil]
  exact (equationAtoms_exact ..).mpr (CommonRoleRecordGraphBridge.common_unfold recordSource 0)

theorem inspection_pending_example : InspectionPending registry (context false) root := by
  apply conservative_deferral registry (context false) root (root_ready false) recursiveHead
    (by simp) recursive_head_checked rfl
  · apply private_model_not_failed constructors _ _ _ [(0, 0)] (root_arguments false) unfinished_report.2 recordModel
    apply (GeneralCandidateIntervals.propagate_models ..).mpr
    refine ⟨unfinished_model, ?_⟩
    rw [unfinished_report.1]
    intro name named
    simp [CommonRoleCandidateConstraints.names] at named
  · exact blocked_unprepared _ _ _ recursive_head_checked [(0, 0)]
      (root_arguments false) descendant_inspection_deferred

theorem recursive_survivor : Survivor registry (context true) root 40 [] := by
  refine ⟨root_ready true, recursiveHead, by simp, recursive_head_checked, rfl, rfl, ?_, ?_⟩
  · obtain ⟨bounds, located, finished, feasible⟩ := recursive_head_ready
    have equal := Option.some.inj (located.symm.trans (root_arguments true))
    subst bounds
    refine ⟨[(0, 0)], root_arguments true, finished, feasible, ?_, ?_, root_linked true, primitives_compatible⟩
    · rw [recursive_captures]
      exact ⟨GeneralCandidateIntervals.singleton_merge_linked _ 0 (1, 1), fun _ _ => rfl⟩
    · constructor
      · rfl
      · intro emission member
        simp [GeneralCanonicalChildOrder.canonicalEmit,
          GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
          GeneralDeclarationDemands.emitAll] at member
        obtain ⟨clause, impossible, _⟩ := member
        cases impossible
  · simp [GeneralDictionaryEmissionPlans.children, GeneralCanonicalChildOrder.canonicalEmit,
      GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
      GeneralDeclarationDemands.emitAll]

/-- This is the actual nominal source head, retained without an invented
Common encoding. It is deferred even in an otherwise ready record snapshot. -/
theorem display_application_deferred (resolved : Bool) :
    (report (context resolved) root GeneralDeclarationExamples.display [(0, 0)]).blocked ≠ [] := by
  simp only [report, headQueries, Declaration.normalHead]
  simp [normalizeArgs, normalize, translate, primitives, inspectMany, inspect, blocked, Report.append]

theorem wrap_application_deferred (resolved : Bool) :
    (report (context resolved) root GeneralDeclarationExamples.wrap [(0, 0)]).blocked ≠ [] := by
  simp only [report, headQueries, Declaration.normalHead]
  simp [normalizeArgs, normalize, translate, primitives, inspectMany, inspect, blocked, Report.append]

private theorem display_report (resolved : Bool) :
    (report (context resolved) root GeneralDeclarationExamples.display [(0, 0)]).captures = [] ∧
      (report (context resolved) root GeneralDeclarationExamples.display [(0, 0)]).conflicts = [] := by
  simp only [report, headQueries, Declaration.normalHead]
  simp [normalizeArgs, normalize, translate, primitives, inspectMany, inspect, blocked, Report.append]

abbrev mixedRegistry : Registry := ⟨constructors, roles, [recursiveHead, GeneralDeclarationExamples.display]⟩

theorem K2_with_other_inspection_pending :
    CandidateK2 mixedRegistry (context true) root ∧ InspectionPending mixedRegistry (context true) root := by
  constructor
  · exact ⟨root_ready true, recursiveHead, by simp, recursive_head_checked, rfl,
      recursive_head_ready, rfl, root_linked true, [(0, 0)], root_arguments true,
      recursive_inspection_K2, primitives_compatible⟩
  · apply conservative_deferral mixedRegistry (context true) root (root_ready true)
      GeneralDeclarationExamples.display (by simp) GeneralDeclarationExamples.display_checked rfl
    · apply private_model_not_failed constructors _ _ _ [(0, 0)] (root_arguments true) (display_report true).2 recordModel
      apply (GeneralCandidateIntervals.propagate_models ..).mpr
      refine ⟨recursive_state_model, ?_⟩
      rw [(display_report true).1]
      intro name named
      simp [CommonRoleCandidateConstraints.names] at named
    · exact blocked_unprepared _ _ _ GeneralDeclarationExamples.display_checked [(0, 0)]
        (root_arguments true) (display_application_deferred true)

end Yulang.GeneralCandidateExamples
