import Yulang.CommonRoleFiniteShadowObstruction

/-! An upper evidence semantics with arbitrary Common substitutions, and
without either rejection gate or candidate uniqueness. It still reads all
actual head/where fields. Even this larger judgment has precisely the same
success set on the finite counterfamily. -/

namespace Yulang.CommonRoleFiniteShadowSemantic

open CommonRoleLinearClock (Configuration)
open CommonRoleInspectedSemantics (Pattern interpretTerm)
open CommonRoleFiniteShadowRegistry (compile terminalImpl headPattern childPattern required visible head_equivalent)
open CommonRoleRegularRegistry (registry registry_linear)
open CommonRoleLinearEvidence (MachineHalts)

structure Goal where
  role : Nat
  argument : Common.Ty

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Common.Ty) : Option Goal := do
  let [term] := requirement.args | none
  return ⟨requirement.role, ← interpretTerm term assignment⟩

def Matches (implementation : Roles.Impl) (goal : Goal) (assignment : Nat → Common.Ty) : Prop :=
  implementation.role = goal.role ∧ ∃ term type, implementation.head = [term] ∧
    interpretTerm term assignment = some type ∧ Common.Equivalent type goal.argument

mutual
  inductive Derives (visible : List Roles.Impl) : Goal → Prop where
    | impl {goal} (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (children : Children visible assignment implementation.constraints) : Derives visible goal
  inductive Children (visible : List Roles.Impl) : (Nat → Common.Ty) → List Roles.Goal → Prop where
    | nil {assignment} : Children visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (derivation : Derives visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

def goalOf (configuration : Configuration) : Goal :=
  ⟨configuration.role, Common.required 0 configuration.value.eval⟩

@[simp] theorem child_interpreted (rule : CommonRoleLinearClock.Rule) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨rule.target, [(childPattern rule).encode]⟩ assignment =
      some ⟨rule.target, Common.required 0 (rule.right.eval assignment)⟩ := by
  simp [interpretGoal, childPattern, required, Pattern.eval, CommonRoleInspectedSemantics.lift_eval, Common.required]

theorem reflect (code : CommonRoleComputation.Code) {goal : Goal} (derivation : Derives (visible code) goal) :
    ∀ source, goal.role = source.role → Common.Equivalent goal.argument (Common.required 0 source.value.eval) →
      MachineHalts (registry code) 0 source := by
  induction derivation using Derives.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      ∀ source, child.role = source.role → Common.Equivalent child.argument (Common.required 0 source.value.eval) →
        MachineHalts (registry code) 0 source) with
  | @impl goal implementation assignment member matched children ih =>
      intro source role data
      rcases List.mem_cons.mp member with rfl | member
      · exact .done (role.symm.trans matched.1.symm)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨sourceRole, term, type, head, interpreted, matched⟩ := matched
        have termEqual : term = (headPattern entry.2).encode := (List.cons.inj head).1.symm
        subst term
        have typeEqual := Option.some.inj
          ((CommonRoleInspectedSemantics.interpret_encode (headPattern entry.2) assignment).symm.trans interpreted)
        subst type
        have dataMatch : Common.Equivalent (entry.2.left.eval assignment) source.value.eval := by
          apply (CommonCanonicalShapes.required_equivalent_iff 0 _ _).mp
          exact Common.equivalent_trans (Common.equivalent_symm (head_equivalent entry.2 assignment))
            (Common.equivalent_trans matched data)
        obtain ⟨target, transition, sameChild⟩ := CommonRoleFiniteShadowHalting.matched_step entry.2
          (registry_linear code entry present) source assignment (sourceRole.trans role) dataMatch
        obtain ⟨child, read, reflected⟩ := ih _ (List.mem_singleton_self _)
        have childEqual := Option.some.inj ((child_interpreted entry.2 assignment).symm.trans read)
        subst child
        have targetRole : entry.2.target = target.role := by
          obtain ⟨_, _, same, _, _⟩ := transition
          exact same.symm
        exact .step entry present transition (reflected target targetRole
          ((CommonCanonicalShapes.required_equivalent_iff 0 _ _).mpr sameChild))
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem of_machine (code : CommonRoleComputation.Code) {source : Configuration}
    (run : MachineHalts (registry code) 0 source) : Derives (visible code) (goalOf source) := by
  induction run with
  | @done source finished =>
      let assignment : Nat → Common.Ty := fun _ => source.value.eval
      exact .impl terminalImpl assignment (List.mem_cons_self ..)
        ⟨finished.symm, _, _, rfl, CommonRoleInspectedSemantics.interpret_encode (required (.var 0)) assignment,
          Common.equivalent_refl _⟩ .nil
  | @step source target entry present transition rest ih =>
      obtain ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩ := transition
      let semantic : Nat → Common.Ty := fun name => (assignment name).eval
      have sourceEval : entry.2.left.eval semantic = source.value.eval := by
        simpa only [CommonRoleLinearClock.instantiate_eval] using congrArg CommonRoleLinearClock.Ground.eval sourceData
      have targetEval : entry.2.right.eval semantic = target.value.eval := by
        simpa only [CommonRoleLinearClock.instantiate_eval] using congrArg CommonRoleLinearClock.Ground.eval targetData
      refine .impl (compile (entry.1 + 1) entry.2) semantic
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, present, rfl⟩)) ?_
        (.cons _ (goalOf target) [] ?_ ih .nil)
      · refine ⟨sourceRole.symm, _, _, rfl,
          CommonRoleInspectedSemantics.interpret_encode (headPattern entry.2) semantic, ?_⟩
        have same := head_equivalent entry.2 semantic
        rw [sourceEval] at same
        exact same
      · rw [child_interpreted, targetEval]
        simp [goalOf, targetRole]

theorem arbitrary_common_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Derives (visible code) (goalOf (CommonRoleRegularHalting.start code input)) ↔ CommonRoleComputation.Halts code input := by
  constructor
  · intro derivation
    exact (CommonRoleRegularHalting.machine_halts_exact code input).mp
      (reflect code derivation _ rfl (Common.equivalent_refl _))
  · intro halting
    exact of_machine code ((CommonRoleRegularHalting.machine_halts_exact code input).mpr halting)

theorem guarded_iff_arbitrary_common (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (CommonRoleInspectedSemantics.Dictionary (visible code) (CommonRoleFiniteShadowHalting.startGoal code input)) ↔
      Derives (visible code) (goalOf (CommonRoleRegularHalting.start code input)) :=
  (CommonRoleFiniteShadowHalting.dictionary_exact code input).trans (arbitrary_common_exact code input).symm

end Yulang.CommonRoleFiniteShadowSemantic
