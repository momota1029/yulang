import Yulang.CommonRoleCanonicalMergedEvidence

/-! Canonical visible captures and the actual merged-row declarations still
encode arbitrary finite programs. No record residual, unresolved goal, or
recursive type participates in this reduction. -/
namespace Yulang.CommonRoleMergedHalting

open CommonRoleLinearClock (Rule Configuration)
open CommonRoleMergedPayload
open CommonRoleMergedRegistry
open CommonRoleCanonicalMergedEvidence
open CommonRoleRegularRegistry (registry)
open CommonRoleLinearEvidence (MachineHalts)

def goalOf (configuration : Configuration) : Goal := ⟨configuration.role, configuration.value⟩
def configurationOf (goal : Goal) : Configuration := ⟨goal.role, goal.value⟩

theorem unique_terminal (code : CommonRoleComputation.Code) (source : Configuration) (finished : source.role = 0) :
    Unique (visible code) terminalImpl (goalOf source) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨substitution, matched⟩ := matched
    obtain ⟨sourceRole, dataMatch⟩ := (matches_compile _ _ _ _).mp matched
    let target : Configuration := ⟨entry.2.target, entry.2.right.instantiate substitution⟩
    have step : entry.2.Step source target := ⟨substitution, sourceRole.symm, rfl, dataMatch, rfl⟩
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1 finished entry present target step)

theorem unique_compile (code : CommonRoleComputation.Code) (source target : Configuration)
    (entry : Nat × Rule) (present : entry ∈ registry code) (step : entry.2.Step source target) :
    Unique (visible code) (compile (entry.1 + 1) entry.2) (goalOf source) := by
  intro other member matched
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨substitution, matched⟩ := matched
    have finished := ((matches_terminal _ _).mp matched).1.symm
    exact False.elim ((CommonRoleRegularRegistry.no_overlap code source).1 finished entry present target step)
  · obtain ⟨other, otherPresent, rfl⟩ := List.mem_map.mp member
    obtain ⟨substitution, matched⟩ := matched
    obtain ⟨sourceRole, dataMatch⟩ := (matches_compile _ _ _ _).mp matched
    let otherTarget : Configuration := ⟨other.2.target, other.2.right.instantiate substitution⟩
    have otherStep : other.2.Step source otherTarget := ⟨substitution, sourceRole.symm, rfl, dataMatch, rfl⟩
    have same := (CommonRoleRegularRegistry.no_overlap code source).2
      other otherPresent entry present otherTarget target otherStep step
    cases same
    rfl

theorem machine_to_dictionary (code : CommonRoleComputation.Code) {source : Configuration}
    (run : MachineHalts (registry code) 0 source) : Nonempty (Dictionary (visible code) (goalOf source)) := by
  induction run with
  | @done source finished =>
      let substitution : Nat → CommonRoleLinearClock.Ground := fun _ => source.value
      exact ⟨.impl terminalImpl substitution (List.mem_cons_self ..)
        ((matches_terminal _ _).mpr ⟨finished.symm, rfl⟩) (unique_terminal code source finished) .nil⟩
  | @step source target entry present transition rest ih =>
      obtain ⟨substitution, sourceRole, targetRole, sourceData, targetData⟩ := transition
      obtain ⟨child⟩ := ih
      have read : interpretGoal ⟨entry.2.target, [plainTerm entry.2.right]⟩ substitution = some (goalOf target) := by
        simp [child_interpreted, goalOf, targetData, targetRole]
      have transition : entry.2.Step source target := ⟨substitution, sourceRole, targetRole, sourceData, targetData⟩
      exact ⟨.impl (compile (entry.1 + 1) entry.2) substitution
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, present, rfl⟩))
        ((matches_compile _ _ _ _).mpr ⟨sourceRole.symm, sourceData⟩)
        (unique_compile code source target entry present transition)
        (.cons _ _ [] read child .nil)⟩

theorem dictionary_to_machine (code : CommonRoleComputation.Code) {goal : Goal}
    (dictionary : Dictionary (visible code) goal) : MachineHalts (registry code) 0 (configurationOf goal) := by
  induction dictionary using Dictionary.rec (motive_2 := fun substitution requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement substitution = some child ∧
      MachineHalts (registry code) 0 (configurationOf child)) with
  | @impl goal implementation substitution member matched unique children ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .done (((matches_terminal _ _).mp matched).1.symm)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨role, data⟩ := (matches_compile _ _ _ _).mp matched
        obtain ⟨child, read, reflected⟩ := ih _ (List.mem_singleton_self _)
        have equal := Option.some.inj ((child_interpreted entry.2 substitution).symm.trans read)
        subst child
        exact .step entry present ⟨substitution, role.symm, rfl, data, rfl⟩ reflected
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem dictionary_iff_machine (code : CommonRoleComputation.Code) (configuration : Configuration) :
    Nonempty (Dictionary (visible code) (goalOf configuration)) ↔ MachineHalts (registry code) 0 configuration :=
  ⟨fun ⟨dictionary⟩ => dictionary_to_machine code dictionary, machine_to_dictionary code⟩

def startGoal (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) : Goal :=
  goalOf (CommonRoleRegularHalting.start code input)

theorem dictionary_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (Dictionary (visible code) (startGoal code input)) ↔ CommonRoleComputation.Halts code input :=
  (dictionary_iff_machine code _).trans (CommonRoleRegularHalting.machine_halts_exact code input)

theorem actual_plan_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    (∃ dictionary : Dictionary (visible code) (startGoal code input),
      ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible code) ↔
      CommonRoleComputation.Halts code input :=
  ⟨fun ⟨dictionary, _⟩ => (dictionary_exact code input).mp ⟨dictionary⟩,
    fun halting => let ⟨dictionary⟩ := (dictionary_exact code input).mpr halting; ⟨dictionary, dictionary.all_visible⟩⟩

end Yulang.CommonRoleMergedHalting
