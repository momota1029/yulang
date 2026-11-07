import Yulang.CommonRoleFiniteShadowRegistry

/-! Exact finite dictionaries for the entirely finite shadow-padding family.
No recursive type, recursive constructor inspection, fuel or role rank is
needed. Candidate uniqueness quantifies arbitrary Common substitutions. -/

namespace Yulang.CommonRoleFiniteShadowHalting

open CommonRoleLinearClock (Rule Linear Ground Configuration)
open CommonRoleInspectedSemantics
open CommonRoleFiniteShadowRegistry
open CommonRoleRegularRegistry (registry registry_linear)
open CommonRoleLinearEvidence (MachineHalts)

theorem matched_step (rule : Rule) (linear : Linear rule) (source : Configuration)
    (assignment : Nat → Common.Ty) (role : rule.source = source.role)
    (matched : Common.Equivalent (rule.left.eval assignment) source.value.eval) :
    ∃ target : Configuration, rule.Step source target ∧
      Common.Equivalent (rule.right.eval assignment) target.value.eval := by
  obtain ⟨head, child⟩ := CommonRoleLinearClock.finite_match_reflection rule linear source.value assignment matched
  let finite := CommonRoleLinearClock.matchingAssignment rule.left source.value
  exact ⟨⟨rule.target, rule.right.instantiate finite⟩, ⟨finite, role.symm, rfl, head, rfl⟩, child⟩

theorem unique_terminal (code : CommonRoleComputation.Code) (source : Configuration) (role : Nat)
    (value : Description) (sameRole : role = source.role) (sameValue : Common.Equivalent value.eval source.value.eval)
    (finished : role = 0) : Unique (visible code) terminalImpl (dataGoal role value) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨assignment, matched⟩ := matched
    obtain ⟨sourceRole, dataMatch⟩ := (matches_compile _ _ _ _ _).mp matched
    obtain ⟨target, step, _⟩ := matched_step entry.2 (registry_linear code entry present) source assignment
      (sourceRole.trans sameRole) (Common.equivalent_trans dataMatch sameValue)
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1
      (sameRole.symm.trans finished) entry present target step)

theorem unique_compile (code : CommonRoleComputation.Code) (source target : Configuration)
    (entry : Nat × Rule) (present : entry ∈ registry code) (transition : entry.2.Step source target)
    (role : Nat) (value : Description) (sameRole : role = source.role)
    (sameValue : Common.Equivalent value.eval source.value.eval) :
    Unique (visible code) (compile (entry.1 + 1) entry.2) (dataGoal role value) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨assignment, matched⟩ := matched
    have finished := ((matches_terminal _ _ _).mp matched).1.symm
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1
      (sameRole.symm.trans finished) entry present target transition)
  · obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp member
    obtain ⟨assignment, matched⟩ := matched
    obtain ⟨sourceRole, dataMatch⟩ := (matches_compile _ _ _ _ _).mp matched
    obtain ⟨otherTarget, otherStep, _⟩ := matched_step other.2 (registry_linear code other otherPresent)
      source assignment (sourceRole.trans sameRole) (Common.equivalent_trans dataMatch sameValue)
    have same := (CommonRoleRegularRegistry.no_overlap code source).2
      other otherPresent entry present otherTarget target otherStep transition
    cases same
    rfl

theorem instantiate_lift_finite (pattern : CommonRoleLinearClock.Pattern) (assignment : Nat → Description)
    (finite : ∀ name, (assignment name).finite = true) :
    (instantiate (liftPattern pattern) assignment).finite = true := by
  induction pattern <;> simp_all [liftPattern, instantiate, Description.finite]

theorem machine_to_dictionary (code : CommonRoleComputation.Code) {source : Configuration}
    (run : MachineHalts (registry code) 0 source) :
    ∀ role value, value.finite = true → role = source.role → Common.Equivalent value.eval source.value.eval →
      Nonempty (Dictionary (visible code) (dataGoal role value)) := by
  induction run with
  | @done source finished =>
      intro role value finite sameRole sameValue
      let assignment : Nat → Description := fun _ => value
      have headMatches : Matches terminalImpl (dataGoal role value) (fun name => (assignment name).eval) :=
        (matches_terminal _ _ _).mpr ⟨(sameRole.trans finished).symm, Common.equivalent_refl _⟩
      exact ⟨.impl (finite_ready _ _ (by simpa [dataGoal, Description.finite] using finite)) terminalImpl assignment
        (List.mem_cons_self ..) headMatches (unique_terminal code source role value sameRole sameValue
          (sameRole.trans finished)) .nil⟩
  | @step source target entry present transition rest ih =>
      intro role value finite sameRole sameValue
      obtain ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩ := transition
      let descriptions : Nat → Description := fun name => .ground (assignment name)
      have headMatches : Matches (compile (entry.1 + 1) entry.2) (dataGoal role value)
          (fun name => (descriptions name).eval) := by
        apply (matches_compile _ _ _ _ _).mpr
        constructor
        · exact sourceRole.symm.trans sameRole.symm
        · have sourceDataEval := congrArg Ground.eval sourceData
          rw [CommonRoleLinearClock.instantiate_eval] at sourceDataEval
          have sourceSame : Common.Equivalent
              (entry.2.left.eval (fun name => (assignment name).eval)) source.value.eval := by
            rw [sourceDataEval]
            exact Common.equivalent_refl _
          exact Common.equivalent_trans sourceSame
            (Common.equivalent_symm sameValue)
      have allFinite : ∀ name, (descriptions name).finite = true := fun _ => rfl
      have childFinite := instantiate_lift_finite entry.2.right descriptions allFinite
      have childSame : Common.Equivalent (instantiate (liftPattern entry.2.right) descriptions).eval target.value.eval := by
        rw [instantiate_eval, lift_eval]
        have targetDataEval := congrArg Ground.eval targetData
        rw [CommonRoleLinearClock.instantiate_eval] at targetDataEval
        change Common.Equivalent (entry.2.right.eval (fun name => (assignment name).eval)) target.value.eval
        rw [targetDataEval]
        exact Common.equivalent_refl _
      obtain ⟨child⟩ := ih _ _ childFinite targetRole.symm childSame
      have transition : entry.2.Step source target := ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩
      exact ⟨.impl (finite_ready _ _ (by simpa [dataGoal, Description.finite] using finite))
        (compile (entry.1 + 1) entry.2) descriptions
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, present, rfl⟩)) headMatches
        (unique_compile code source target entry present transition role value sameRole sameValue)
        (.cons _ _ [] (child_interpreted entry.2 descriptions) child .nil)⟩

theorem dictionary_to_machine (code : CommonRoleComputation.Code) {goal : Goal}
    (dictionary : Dictionary (visible code) goal) :
    ∀ source role value, goal = dataGoal role value → role = source.role →
      Common.Equivalent value.eval source.value.eval → MachineHalts (registry code) 0 source := by
  induction dictionary using Dictionary.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      ∀ source role value, child = dataGoal role value → role = source.role →
        Common.Equivalent value.eval source.value.eval → MachineHalts (registry code) 0 source) with
  | @impl goal ready implementation assignment member matched unique children ih =>
      intro source role value equal sameRole sameValue
      subst goal
      rcases List.mem_cons.mp member with rfl | member
      · have finished := ((matches_terminal _ _ _).mp matched).1.symm
        exact .done (sameRole.symm.trans finished)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨sourceRole, dataMatch⟩ := (matches_compile _ _ _ _ _).mp matched
        obtain ⟨target, transition, childSame⟩ := matched_step entry.2 (registry_linear code entry present)
          source (fun name => (assignment name).eval) (sourceRole.trans sameRole)
          (Common.equivalent_trans dataMatch sameValue)
        obtain ⟨child, interpreted, reflected⟩ := ih _ (List.mem_singleton_self _)
        have childEqual := Option.some.inj ((child_interpreted entry.2 assignment).symm.trans interpreted)
        have roleEqual : entry.2.target = target.role := by
          obtain ⟨_, _, role, _, _⟩ := transition
          exact role.symm
        have valueSame : Common.Equivalent (instantiate (liftPattern entry.2.right) assignment).eval target.value.eval := by
          rw [instantiate_eval, lift_eval]
          exact childSame
        exact .step entry present transition (reflected target _ _ childEqual.symm roleEqual valueSame)
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

def goalOf (configuration : Configuration) : Goal := dataGoal configuration.role (.ground configuration.value)

theorem dictionary_iff_machine (code : CommonRoleComputation.Code) (configuration : Configuration) :
    Nonempty (Dictionary (visible code) (goalOf configuration)) ↔ MachineHalts (registry code) 0 configuration := by
  constructor
  · rintro ⟨dictionary⟩
    exact dictionary_to_machine code dictionary configuration _ _ rfl rfl (Common.equivalent_refl _)
  · intro run
    exact machine_to_dictionary code run _ _ rfl rfl (Common.equivalent_refl _)

def startGoal (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) : Goal :=
  dataGoal 1 (.pair (.ground code.encode)
    (.pair (.data input) (.ground CommonRoleLinearInterpreter.Kont.halt.encode)))

theorem start_finite (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (startGoal code input).argument.finite = true := rfl

theorem dictionary_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (Dictionary (visible code) (startGoal code input)) ↔ CommonRoleComputation.Halts code input := by
  constructor
  · rintro ⟨dictionary⟩
    exact (CommonRoleRegularHalting.machine_halts_exact code input).mp
      (dictionary_to_machine code dictionary (CommonRoleRegularHalting.start code input) _ _ rfl rfl
        (Common.equivalent_refl _))
  · intro halting
    exact machine_to_dictionary code ((CommonRoleRegularHalting.machine_halts_exact code input).mpr halting)
      _ _ rfl rfl (Common.equivalent_refl _)

theorem actual_plan_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (∃ dictionary : Dictionary (visible code) (startGoal code input),
      ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible code) ↔
      CommonRoleComputation.Halts code input := by
  constructor
  · rintro ⟨dictionary, _⟩
    exact (dictionary_exact code input).mp ⟨dictionary⟩
  · intro halting
    obtain ⟨dictionary⟩ := (dictionary_exact code input).mpr halting
    exact ⟨dictionary, dictionary.all_visible⟩

end Yulang.CommonRoleFiniteShadowHalting
