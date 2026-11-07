import Yulang.CommonRoleFiniteTailRegistry

/-! The normalized, entirely finite tail-clock registry has a finite real
dictionary exactly when the encoded finite program terminates. All candidate
uniqueness claims cover arbitrary Common substitutions. -/
namespace Yulang.CommonRoleFiniteTailHalting

open CommonRoleLinearClock (Configuration Rule)
open CommonRoleInspectedSemantics
open CommonRoleFiniteTailClock
open CommonRoleFiniteTailRegistry
open CommonRoleRegularRegistry (registry registry_linear)
open CommonRoleLinearEvidence (MachineHalts)
open CommonRoleFiniteShadowHalting (matched_step instantiate_lift_finite)

attribute [local irreducible] count

theorem unique_terminal (code : CommonRoleComputation.Code) (source : Configuration) (role : Nat)
    (clockType value : Description) (sameRole : role = source.role)
    (sameValue : Common.Equivalent value.eval source.value.eval) (finished : role = 0) :
    Unique (visible code) terminalImpl (pairGoal role clockType value) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨substitution, matched⟩ := matched
    obtain ⟨sourceRole, _, dataMatch⟩ := (matches_compile _ _ _ _ _ _ _).mp matched
    obtain ⟨target, step, _⟩ := matched_step entry.2 (registry_linear code entry present) source substitution
      (sourceRole.trans sameRole) (Common.equivalent_trans dataMatch sameValue)
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1
      (sameRole.symm.trans finished) entry present target step)

theorem unique_compile (code : CommonRoleComputation.Code) (source target : Configuration)
    (entry : Nat × Rule) (present : entry ∈ registry code) (transition : entry.2.Step source target)
    (role : Nat) (clockType value : Description) (sameRole : role = source.role)
    (sameValue : Common.Equivalent value.eval source.value.eval) :
    Unique (visible code) (compile (count code) (entry.1 + 1) entry.2) (pairGoal role clockType value) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨substitution, matched⟩ := matched
    have finished := ((matches_terminal _ _ _ _).mp matched).1.symm
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1
      (sameRole.symm.trans finished) entry present target transition)
  · obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp member
    obtain ⟨substitution, matched⟩ := matched
    obtain ⟨sourceRole, _, dataMatch⟩ := (matches_compile _ _ _ _ _ _ _).mp matched
    obtain ⟨otherTarget, otherStep, _⟩ := matched_step other.2 (registry_linear code other otherPresent)
      source substitution (sourceRole.trans sameRole) (Common.equivalent_trans dataMatch sameValue)
    have same := (CommonRoleRegularRegistry.no_overlap code source).2
      other otherPresent entry present otherTarget target otherStep transition
    cases same
    rfl

def dataGoal (code : CommonRoleComputation.Code) (role : Nat) (value : Description) : Goal :=
  pairGoal role (clock (count code)) value

theorem machine_to_dictionary (code : CommonRoleComputation.Code) {source : Configuration}
    (run : MachineHalts (registry code) 0 source) :
    ∀ role value, value.finite = true → role = source.role → Common.Equivalent value.eval source.value.eval →
      Nonempty (Dictionary (visible code) (dataGoal code role value)) := by
  induction run with
  | @done source finished =>
      intro role value finite sameRole sameValue
      let substitution : Nat → Description := fun name => if name = 0 then clock (count code) else value
      have headMatch : Matches terminalImpl (dataGoal code role value) (fun name => (substitution name).eval) := by
        apply (matches_terminal _ _ _ _).mpr
        exact ⟨(sameRole.trans finished).symm, Common.equivalent_refl _, Common.equivalent_refl _⟩
      exact ⟨.impl (finite_ready _ _ (by simp [dataGoal, pairGoal, Description.finite, clock_finite, finite]))
        terminalImpl substitution (List.mem_cons_self ..) headMatch
        (unique_terminal code source role _ value sameRole sameValue (sameRole.trans finished)) .nil⟩
  | @step source target entry present transition rest ih =>
      intro role value finite sameRole sameValue
      obtain ⟨substitution, sourceRole, targetRole, sourceData, targetData⟩ := transition
      let descriptions := assignment entry.2 substitution
      have headMatch : Matches (compile (count code) (entry.1 + 1) entry.2) (dataGoal code role value)
          (fun name => (descriptions name).eval) := by
        apply (matches_compile _ _ _ _ _ _ _).mpr
        refine ⟨sourceRole.symm.trans sameRole.symm, head_clock_matches _ _ _ (assignment_fresh _ _), ?_⟩
        have data := assignment_data entry.2 entry.2.left (Nat.le_max_left ..) substitution
        rw [sourceData] at data
        exact Common.equivalent_trans data (Common.equivalent_symm sameValue)
      have childFinite := instantiate_lift_finite entry.2.right descriptions (assignment_finite _ _)
      have childSame : Common.Equivalent (instantiate (liftPattern entry.2.right) descriptions).eval target.value.eval := by
        rw [instantiate_eval, lift_eval]
        have data := assignment_data entry.2 entry.2.right (Nat.le_max_right ..) substitution
        rw [targetData] at data
        exact data
      obtain ⟨child⟩ := ih _ _ childFinite targetRole.symm childSame
      have interpreted : interpretGoal ⟨entry.2.target, [(childPattern (count code) entry.2).encode]⟩ descriptions =
          some (dataGoal code entry.2.target (instantiate (liftPattern entry.2.right) descriptions)) := by
        rw [child_interpreted]
        simp only [descriptions, assignment_fresh, dataGoal, clock]
      have transition : entry.2.Step source target := ⟨substitution, sourceRole, targetRole, sourceData, targetData⟩
      exact ⟨.impl (finite_ready _ _ (by simp [dataGoal, pairGoal, Description.finite, clock_finite, finite]))
        (compile (count code) (entry.1 + 1) entry.2) descriptions
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, present, rfl⟩)) headMatch
        (unique_compile code source target entry present transition role _ value sameRole sameValue)
        (.cons _ _ [] interpreted child .nil)⟩

theorem dictionary_to_machine (code : CommonRoleComputation.Code) {goal : Goal}
    (dictionary : Dictionary (visible code) goal) :
    ∀ source role clockType value, goal = pairGoal role clockType value → role = source.role →
      Common.Equivalent value.eval source.value.eval → MachineHalts (registry code) 0 source := by
  induction dictionary using Dictionary.rec (motive_2 := fun substitution requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement substitution = some child ∧
      ∀ source role clockType value, child = pairGoal role clockType value → role = source.role →
        Common.Equivalent value.eval source.value.eval → MachineHalts (registry code) 0 source) with
  | @impl goal ready implementation substitution member matched unique children ih =>
      intro source role clockType value equal sameRole sameValue
      subst goal
      rcases List.mem_cons.mp member with rfl | member
      · have finished := ((matches_terminal _ _ _ _).mp matched).1.symm
        exact .done (sameRole.symm.trans finished)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨sourceRole, _, dataMatch⟩ := (matches_compile _ _ _ _ _ _ _).mp matched
        obtain ⟨target, transition, childSame⟩ := matched_step entry.2 (registry_linear code entry present)
          source (fun name => (substitution name).eval) (sourceRole.trans sameRole)
          (Common.equivalent_trans dataMatch sameValue)
        obtain ⟨child, interpreted, reflected⟩ := ih _ (List.mem_singleton_self _)
        have childEqual := Option.some.inj ((child_interpreted (count code) entry.2 substitution).symm.trans interpreted)
        have roleEqual : entry.2.target = target.role := by
          obtain ⟨_, _, role, _, _⟩ := transition
          exact role.symm
        have valueSame : Common.Equivalent (instantiate (liftPattern entry.2.right) substitution).eval target.value.eval := by
          rw [instantiate_eval, lift_eval]
          exact childSame
        exact .step entry present transition (reflected target _ _ _ childEqual.symm roleEqual valueSame)
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

def goalOf (code : CommonRoleComputation.Code) (configuration : Configuration) : Goal :=
  dataGoal code configuration.role (.ground configuration.value)

theorem dictionary_iff_machine (code : CommonRoleComputation.Code) (configuration : Configuration) :
    Nonempty (Dictionary (visible code) (goalOf code configuration)) ↔ MachineHalts (registry code) 0 configuration :=
  ⟨fun ⟨dictionary⟩ => dictionary_to_machine code dictionary configuration _ _ _ rfl rfl (Common.equivalent_refl _),
    fun run => machine_to_dictionary code run _ _ rfl rfl (Common.equivalent_refl _)⟩

def startGoal (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) : Goal :=
  dataGoal code 1 (.pair (.ground code.encode) (.pair (.data input) (.ground CommonRoleLinearInterpreter.Kont.halt.encode)))

theorem start_finite (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (startGoal code input).argument.finite = true := by
  simp [startGoal, dataGoal, pairGoal, Description.finite, clock_finite]

theorem dictionary_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (Dictionary (visible code) (startGoal code input)) ↔ CommonRoleComputation.Halts code input := by
  constructor
  · rintro ⟨dictionary⟩
    exact (CommonRoleRegularHalting.machine_halts_exact code input).mp
      (dictionary_to_machine code dictionary (CommonRoleRegularHalting.start code input) _ _ _ rfl rfl
        (Common.equivalent_refl _))
  · intro halting
    exact machine_to_dictionary code ((CommonRoleRegularHalting.machine_halts_exact code input).mpr halting)
      _ _ rfl rfl (Common.equivalent_refl _)

theorem actual_plan_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (∃ dictionary : Dictionary (visible code) (startGoal code input),
      ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible code) ↔
      CommonRoleComputation.Halts code input :=
  ⟨fun ⟨dictionary, _⟩ => (dictionary_exact code input).mp ⟨dictionary⟩,
    fun halting => let ⟨dictionary⟩ := (dictionary_exact code input).mpr halting; ⟨dictionary, dictionary.all_visible⟩⟩

end Yulang.CommonRoleFiniteTailHalting
