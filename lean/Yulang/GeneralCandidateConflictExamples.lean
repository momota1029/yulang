import Yulang.GeneralCandidateExamples

/-!
# Known-head interval failure and whole-demand deferral

Both intervals below have a known lower head and are individually valid.
Their repeated-variable cross constraints fail in the ordinary solver. The
same general demand with its second lower head unresolved instead stays pending.
-/
namespace Yulang.GeneralCandidateConflictExamples

open GeneralSourceState (State Assignment Models equationAtoms equationAtoms_exact)
open GeneralSourceStateExamples (indexAfter indexAfterHeads indexState indexModel)
open GeneralCandidateInspection GeneralCandidateBoundaryParts
open GeneralDeclarations GeneralDeclarationPatterns
open Core.PresenceGeneration (TyTerm)
open GeneralCandidateExamples (roles constructors frame primitives)

abbrev afterView : GeneralNormalizedObservation.Snapshot indexAfter where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := fun i => Fin.elim0 i
  heads := fun slot => if slot = 0 then .scalar .str else if slot = 1 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : (.base .str : TyTerm (Fin 3)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head rfl
    · by_cases one : slot = 1
      · subst slot
        have equal : (.base .int : TyTerm (Fin 3)) = term := by
          simpa [GeneralNormalizedObservation.Head.term] using recorded
        subst term
        exact .head rfl
      · simp [zero, one, GeneralNormalizedObservation.Head.term,
          GeneralNormalizedObservation.Deferred.term] at recorded

abbrev context : Context roles := ⟨indexAfter, primitives, afterView, fun _ => frame, fun _ _ _ => (0, 0)⟩
abbrev before : Context roles :=
  ⟨indexState, primitives, GeneralSourceK2Examples.indexView, fun _ => frame, fun _ _ _ => (0, 0)⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨101, ⟨4, fun i => if i.val = 0 then (0, 0) else (1, 1), [], by intro output member; cases member⟩⟩
abbrev repeated : Declaration := ⟨41, 4, [.var 0, .var 0], [], [], []⟩
abbrev registry : Registry := ⟨constructors, roles, [repeated]⟩
abbrev bindings : GeneralCandidateIntervals.Bindings indexAfter := [(0, (0, 0)), (0, (1, 1))]

theorem repeated_checked : DeclarationChecked constructors roles repeated := by
  constructor
  · simp [Declaration.Signature, roles, GeneralDeclarationExamples.roles, GeneralDeclarationExamples.binaryRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped]
  all_goals intro clause member; cases member

private theorem covered : GeneralCandidateIntervals.Covered indexAfter := by
  constructor
  · simp [PresenceGeneratedChildGrammar.GoodAtoms, PresenceGeneratedChildGrammar.GoodAtom,
      PresenceGeneratedChildGrammar.lower, PresenceGeneratedChildGrammar.upper, indexAfter, equationAtoms]
  · intro source target member tail needed
    simp [indexAfter, equationAtoms] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases needed
  · simp [PresenceSourceConstraintSupport.GoodAtoms, PresenceSourceConstraintSupport.GoodAtom,
      PresenceSourceConstraintSupport.simpleTyRows, indexAfter, equationAtoms]
  · exact fun _ _ equal => Fin.ext equal

theorem repeated_capture :
    (report context root repeated [(0, 0), (1, 1)]).captures = bindings := by
  simp [report, headQueries, Declaration.normalHead, normalizeArgs, normalize, translate,
    inspectMany, inspect, Report.append, bindings]

theorem known_arguments : arguments context root = some [(0, 0), (1, 1)] := by decide +kernel

theorem known_lower_heads : ¬ RootPending context root := by
  rintro ⟨argument, _, unknown⟩
  by_cases zero : argument.val = 0
  · exact unknown ⟨0, by simp [zero], by simp [GeneralNormalizedObservation.Snapshot.graph,
      GeneralNormalizedObservation.Head.node]⟩
  · exact unknown ⟨1, by simp [zero], by simp [GeneralNormalizedObservation.Snapshot.graph,
      GeneralNormalizedObservation.Head.node]⟩

theorem original_has_model : Models indexAfter (indexModel (.base .int)) := by
  apply (GeneralSourceState.models_ordinary ..).mpr
  apply (PresenceNormalForm.all_append ..).mpr
  constructor <;> apply (equationAtoms_exact ..).mpr <;> exact Common.equivalent_refl _

theorem cross_constraints_eliminate : GeneralCandidateIntervals.Eliminated indexAfter bindings := by
  refine ⟨covered, ?_⟩
  apply (CommonRoleCandidateConstraints.solve_empty_exact _ _ covered.child covered.width covered.rows).mpr
  rintro ⟨assignment, ordinary, compatible⟩
  have both := (PresenceNormalForm.all_append ..).mp ordinary
  have str := (equationAtoms_exact 0 (.base .str) assignment).mp both.1
  have int := (equationAtoms_exact 1 (.base .int) assignment).mp both.2
  have cross := compatible 0 (by decide +kernel) (0, 0) (by decide +kernel) (1, 1) (by decide +kernel)
  have impossible : Common.Subtype (.base .str) (.base .int) :=
    Common.subtype_trans str.2 (Common.subtype_trans cross int.1)
  cases (CommonRigidHeadInspection.base_iff .str .int).mp impossible

theorem known_all_candidates_fail :
    (∀ key children, ¬ Survivor registry context root key children) ∧
      ¬ InspectionPending registry context root := by
  apply all_failed_no_survivors
  intro declaration visible _
  have same := List.mem_singleton.mp visible
  subst declaration
  refine ⟨?_, [(0, 0), (1, 1)], known_arguments, Or.inr ?_⟩
  · intro name primitive observed
    by_cases four : name = 4
    · subst name
      have same : Primitive.emptyRecord = primitive := by simpa [primitives] using observed
      subst primitive
      exact ⟨⟨[], 4⟩, rfl, rfl⟩
    · simp [primitives, four] at observed
  · rw [repeated_capture]
    exact cross_constraints_eliminate

/-- The all-input Needed rule applies even though both head positions are
plain variables. A lone implementation cannot determine the second input. -/
theorem unresolved_second_input_pending :
    RootPending before root ∧ ¬ RootK2 before root ∧ ¬ CandidateK2 registry before root := by
  have pending : RootPending before root := by
    refine ⟨⟨1, by decide⟩, GeneralDeclarationDemands.every_input_needed _ _, ?_⟩
    rintro ⟨slot, same, known⟩
    have one : slot = 1 := Fin.ext same
    subst slot
    exact known rfl
  exact ⟨pending, pending_excludes_rootK2 _ _ pending, pending_excludes_candidateK2 _ _ _ pending⟩

end Yulang.GeneralCandidateConflictExamples
