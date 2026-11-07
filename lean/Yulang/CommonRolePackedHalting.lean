import Yulang.CommonRolePackedRegistry

/-! A finite guarded dictionary exists exactly when the original finite
program terminates. Every reached goal is a pair root: the cyclic clock is
never itself a role argument at a resolution invocation. -/

namespace Yulang.CommonRolePackedHalting

open CommonRoleLinearClock
open CommonRoleReachedRoot
open CommonRolePackedRegistry
open CommonRoleLinearEvidence (MachineHalts)
open CommonRoleRegularRegistry (registry registry_linear)

def descriptionAssignment (rule : Rule) (assignment : Nat → Ground) : Nat → Description :=
  fun name => if name = rule.fresh then .clock else .finite (assignment name)

theorem descriptionAssignment_eval (rule : Rule) (assignment : Nat → Ground) :
    assignmentEval (descriptionAssignment rule assignment) = clockAssignment rule assignment := by
  funext name
  by_cases same : name = rule.fresh <;>
    simp [assignmentEval, descriptionAssignment, clockAssignment, same, Description.eval]

theorem finite_step_description (rule : Rule) (source target : Configuration)
    (step : rule.Step source target) :
    ∃ assignment : Nat → Description,
      HeadMatches rule (goalOf source) (assignmentEval assignment) ∧
      GoalEquivalent (childGoal rule (assignmentEval assignment)) (goalOf target) := by
  obtain ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩ := step
  refine ⟨descriptionAssignment rule assignment, ?_, ?_⟩
  all_goals rw [descriptionAssignment_eval]
  · refine ⟨sourceRole.symm, ?_, ?_⟩
    · simpa [headGoal, goalOf, wrapPattern_eval, Pattern.eval, clockAssignment] using wrapped_clock rule.padding
    · simpa [headGoal, goalOf, sourceData] using
        clockAssignment_eval rule rule.left (Nat.le_max_left ..) assignment
  · refine ⟨targetRole.symm, ?_, ?_⟩
    · simp [childGoal, goalOf, clockAssignment, Common.equivalent_refl]
    · simpa [childGoal, goalOf, targetData] using
        clockAssignment_eval rule rule.right (Nat.le_max_right ..) assignment

/-- All arbitrary semantic matches are covered by the old no-overlap proof.
The forward dictionary construction itself uses concrete finite descriptions. -/
theorem machine_to_dictionary (code : CommonRoleComputation.Code) {configuration : Configuration}
    (run : MachineHalts (registry code) 0 configuration) :
    ∀ role first last, GoalEquivalent (semanticGoal role first last) (goalOf configuration) →
      Nonempty (CommonRoleReachedRoot.Dictionary (visible code) (pairGoal role first last)) := by
  induction run with
  | @done configuration finished =>
      intro role first last same
      have roleFinished : role = 0 := same.1.trans finished
      let assignment : Nat → Description := fun name => if name = 0 then first else last
      have matched : CommonRoleReachedRoot.Matches (packImpl (terminalImpl 0 0))
          (pairGoal role first last) assignment := by
        refine ⟨pairGoal 0 first last, ?_, roleFinished.symm, Common.equivalent_refl _⟩
        simp [terminal_head, assignment]
      have noOverlap := CommonRoleLinearEvidence.no_semantic_head_overlap (registry_linear code)
        (CommonRoleRegularRegistry.no_overlap code configuration) same
      have unique : CommonRoleActualEvidence.Unique
          (CommonRoleLinearEvidence.visible (registry code) 0) (terminalImpl 0 0)
          (semanticGoal role first last) := by
        apply (CommonRoleActualEvidence.unique_terminal _ _ _).mpr
        intro entry member assignment matched
        exact noOverlap (Or.inl ⟨roleFinished, entry, member, assignment, matched⟩)
      exact ⟨.impl (pair_not_recursive first last) (packImpl (terminalImpl 0 0)) assignment
        (List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩) matched
        (unique_of_actual code _ role first last unique) .nil⟩
  | @step source target entry member transition rest ih =>
      intro role first last same
      obtain ⟨assignment, matched, sameChild⟩ := finite_step_description entry.2 source target transition
      have rootMatch := GoalEquivalent.trans matched (GoalEquivalent.symm same)
      have noOverlap := CommonRoleLinearEvidence.no_semantic_head_overlap (registry_linear code)
        (CommonRoleRegularRegistry.no_overlap code source) same
      have uniqueHead : CommonRoleLinearEvidence.UniqueHead (registry code) 0 entry
          (semanticGoal role first last) := by
        constructor
        · intro finished
          exact noOverlap (Or.inl ⟨finished, entry, member, assignmentEval assignment, rootMatch⟩)
        · intro other present otherMatch
          by_cases equal : other = entry
          · exact equal
          · exact False.elim (noOverlap (Or.inr ⟨other, present, entry, member, equal,
              otherMatch, assignmentEval assignment, rootMatch⟩))
      have unique := (CommonRoleActualEvidence.unique_compile (registry code) 0 entry
        (semanticGoal role first last)).mpr uniqueHead
      have sameChildDescription : GoalEquivalent
          (semanticGoal entry.2.target (assignment entry.2.fresh) (instantiate entry.2.right assignment))
          (goalOf target) := by
        change GoalEquivalent
          (semanticGoal entry.2.target (assignment entry.2.fresh) (instantiate entry.2.right assignment))
          (goalOf target)
        rw [semanticGoal, CommonRoleReachedRoot.instantiate_eval]
        exact sameChild
      obtain ⟨child⟩ := ih _ _ _ sameChildDescription
      exact ⟨.impl (pair_not_recursive first last) (packImpl (compile (entry.1 + 1) entry.2)) assignment
        (List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩), rfl⟩)
        ((matches_compile _ _ _ _ _ _).mpr rootMatch)
        (unique_of_actual code _ role first last unique)
        (.cons _ _ [] (packed_child entry.2 assignment) child .nil)⟩

/-- Reflection ignores the gate, so even admitting additional substitutions
could not introduce non-halting successful evidence on this family. -/
theorem derives_to_old (code : CommonRoleComputation.Code) {goal : CommonRoleReachedRoot.Goal}
    (derivation : CommonRoleReachedRoot.Derives (visible code) goal) :
    ∀ role first last, goal = pairGoal role first last →
      CommonRoleLinearEvidence.Derives (registry code) 0 (semanticGoal role first last) := by
  induction derivation using CommonRoleReachedRoot.Derives.rec
    (motive_2 := fun assignment requirements _ =>
      ∀ requirement ∈ requirements, ∃ child,
        CommonRoleReachedRoot.interpretGoal requirement assignment = some child ∧
        ∀ role first last, child = pairGoal role first last →
          CommonRoleLinearEvidence.Derives (registry code) 0 (semanticGoal role first last)) with
  | @impl goal safe implementation assignment member matched children ih =>
      intro role first last equal
      subst goal
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      rcases List.mem_cons.mp present with rfl | present
      · have actual := matches_to_actual code _ (List.mem_cons_self ..) role first last assignment matched
        exact .done ((CommonRoleActualEvidence.matches_terminal _ _ _).mp ⟨_, actual⟩)
      · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp present
        obtain ⟨child, interpreted, reflected⟩ := ih _ (List.mem_singleton_self _)
        have equal := Option.some.inj ((packed_child entry.2 assignment).symm.trans interpreted)
        subst child
        have reflected := reflected _ _ _ rfl
        have oldChild : CommonRoleLinearEvidence.Derives (registry code) 0
            (childGoal entry.2 (assignmentEval assignment)) := by
          rw [semanticGoal, CommonRoleReachedRoot.instantiate_eval] at reflected
          exact reflected
        exact .step entry (assignmentEval assignment) entryMember
          ((matches_compile _ _ _ _ _ _).mp matched) oldChild
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

def goalOfDescription (configuration : Configuration) : CommonRoleReachedRoot.Goal :=
  pairGoal configuration.role .clock (.finite configuration.value)

theorem dictionary_iff_machine (code : CommonRoleComputation.Code) (configuration : Configuration) :
    Nonempty (CommonRoleReachedRoot.Dictionary (visible code) (goalOfDescription configuration)) ↔
      MachineHalts (registry code) 0 configuration := by
  constructor
  · rintro ⟨dictionary⟩
    have old := derives_to_old code dictionary.derives _ _ _ rfl
    exact (CommonRoleLinearEvidence.derives_iff_machine_halts _ _ (registry_linear code) configuration).mp old
  · intro run
    exact machine_to_dictionary code run _ _ _ (GoalEquivalent.refl _)

def startGoal (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    CommonRoleReachedRoot.Goal :=
  pairGoal 1 .clock (.pair (.finite code.encode)
    (.pair (.data input) (.finite CommonRoleLinearInterpreter.Kont.halt.encode)))

theorem dictionary_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (CommonRoleReachedRoot.Dictionary (visible code) (startGoal code input)) ↔
      CommonRoleComputation.Halts code input := by
  constructor
  · rintro ⟨dictionary⟩
    have old := derives_to_old code dictionary.derives _ _ _ rfl
    exact (CommonRoleRegularHalting.derives_exact code input).mp old
  · intro halting
    exact machine_to_dictionary code
      ((CommonRoleRegularHalting.machine_halts_exact code input).mpr halting) _ _ _
      (GoalEquivalent.refl _)

theorem no_rejection (code : CommonRoleComputation.Code) (role : Nat)
    (first last : Description) (path : List (Roles.Impl × Nat)) :
    ¬ Rejects (visible code) (pairGoal role first last) path := by
  intro rejected
  have refute {goal : CommonRoleReachedRoot.Goal} {path} (proof : Rejects (visible code) goal path) :
      ∀ role first last, goal = pairGoal role first last → False := by
    induction proof with
    | here recursive =>
        intro role first last same
        subst same
        exact pair_not_recursive first last recursive
    | descend safe implementation assignment index member matched unique requirement present interpreted rejected ih =>
        intro role first last _
        obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
        subst implementation
        have required := List.mem_of_getElem? present
        rcases List.mem_cons.mp originalMember with rfl | originalMember
        · cases required
        · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp originalMember
          have same : requirement = packGoal
              ⟨entry.2.target, [.var entry.2.fresh, entry.2.right.encode]⟩ := by
            simpa [packImpl, compile] using required
          subst requirement
          have childSame := Option.some.inj ((packed_child entry.2 assignment).symm.trans interpreted)
          exact ih _ _ _ childSame.symm
  exact refute rejected role first last rfl

theorem actual_plan_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (∃ dictionary : CommonRoleReachedRoot.Dictionary (visible code) (startGoal code input),
      ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible code) ↔
      CommonRoleComputation.Halts code input := by
  constructor
  · rintro ⟨dictionary, _⟩
    exact (dictionary_exact code input).mp ⟨dictionary⟩
  · intro halting
    obtain ⟨dictionary⟩ := (dictionary_exact code input).mpr halting
    exact ⟨dictionary, dictionary.all_visible⟩

end Yulang.CommonRolePackedHalting
