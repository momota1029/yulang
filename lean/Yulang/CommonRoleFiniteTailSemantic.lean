import Yulang.CommonRoleFiniteTailObstruction

/-! Arbitrary Common substitutions cannot add spurious successes. The upper
semantics is the already independent, actual-field-reading unary Derives,
without either K2 gate or candidate uniqueness. -/
namespace Yulang.CommonRoleFiniteTailSemantic

open CommonRoleInspectedSemantics
open CommonRoleFiniteTailClock
open CommonRoleFiniteTailRegistry
open CommonRoleRegularRegistry (registry registry_linear)
open CommonRoleLinearClock (Configuration)
open CommonRoleLinearEvidence (MachineHalts)

attribute [local irreducible] count

def meaning (goal : Goal) : CommonRoleFiniteShadowSemantic.Goal := ⟨goal.role, goal.argument.eval⟩

theorem interpretGoal_commutes (requirement : Roles.Goal) (substitution : Nat → Description) :
    (interpretGoal requirement substitution).map meaning =
      CommonRoleFiniteShadowSemantic.interpretGoal requirement (fun name => (substitution name).eval) := by
  cases requirement with
  | mk role args =>
      cases args with
      | nil => rfl
      | cons term rest =>
          cases rest with
          | cons _ _ => rfl
          | nil =>
              cases decoded : decodePattern term <;>
                simp [interpretGoal, CommonRoleFiniteShadowSemantic.interpretGoal, interpretDescription, interpretTerm, decoded,
                  meaning, instantiate_eval]

theorem forget (visible : List Roles.Impl) {goal : Goal} (dictionary : Dictionary visible goal) :
    CommonRoleFiniteShadowSemantic.Derives visible (meaning goal) := by
  induction dictionary using Dictionary.rec (motive_2 := fun substitution requirements _ =>
    CommonRoleFiniteShadowSemantic.Children visible (fun name => (substitution name).eval) requirements) with
  | impl ready implementation substitution member matched unique children ih =>
      exact .impl implementation (fun name => (substitution name).eval) member matched ih
  | nil => exact .nil
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      have read := congrArg (Option.map meaning) interpreted
      rw [interpretGoal_commutes] at read
      exact .cons requirement (meaning child) rest read ihChild ihRest

@[simp] theorem child_interpreted (slots : Nat) (rule : CommonRoleLinearClock.Rule) (substitution : Nat → Common.Ty) :
    CommonRoleFiniteShadowSemantic.interpretGoal ⟨rule.target, [(childPattern slots rule).encode]⟩ substitution =
      some ⟨rule.target, Common.pair ((clockChild slots rule.fresh).eval substitution) (rule.right.eval substitution)⟩ := by
  simp [CommonRoleFiniteShadowSemantic.interpretGoal, childPattern, Pattern.eval, lift_eval]

theorem reflect (code : CommonRoleComputation.Code) {goal : CommonRoleFiniteShadowSemantic.Goal} (derivation : CommonRoleFiniteShadowSemantic.Derives (visible code) goal) :
    ∀ source clockType, goal.role = source.role →
      Common.Equivalent goal.argument (Common.pair clockType source.value.eval) → MachineHalts (registry code) 0 source := by
  induction derivation using CommonRoleFiniteShadowSemantic.Derives.rec (motive_2 := fun substitution requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, CommonRoleFiniteShadowSemantic.interpretGoal requirement substitution = some child ∧
      ∀ source clockType, child.role = source.role →
        Common.Equivalent child.argument (Common.pair clockType source.value.eval) → MachineHalts (registry code) 0 source) with
  | @impl goal implementation substitution member matched children ih =>
      intro source clockType role data
      rcases List.mem_cons.mp member with rfl | member
      · exact .done (role.symm.trans matched.1.symm)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨sourceRole, term, type, head, interpreted, matched⟩ := matched
        have termEqual : term = (headPattern (count code) entry.2).encode := (List.cons.inj head).1.symm
        subst term
        have typeEqual := Option.some.inj ((interpret_encode (headPattern (count code) entry.2) substitution).symm.trans interpreted)
        subst type
        have dataMatch : Common.Equivalent (entry.2.left.eval substitution) source.value.eval := by
          have split := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp (Common.equivalent_trans matched data)
          simpa [headPattern, Pattern.eval, lift_eval] using split.2
        obtain ⟨target, transition, sameChild⟩ := CommonRoleFiniteShadowHalting.matched_step entry.2
          (registry_linear code entry present) source substitution (sourceRole.trans role) dataMatch
        obtain ⟨child, read, reflected⟩ := ih _ (List.mem_singleton_self _)
        have childEqual := Option.some.inj ((child_interpreted (count code) entry.2 substitution).symm.trans read)
        subst child
        have targetRole : entry.2.target = target.role := by
          obtain ⟨_, _, same, _, _⟩ := transition
          exact same.symm
        exact .step entry present transition (reflected target _ targetRole
          ((CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨Common.equivalent_refl _, sameChild⟩))
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem arbitrary_common_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    CommonRoleFiniteShadowSemantic.Derives (visible code) (meaning (CommonRoleFiniteTailHalting.startGoal code input)) ↔ CommonRoleComputation.Halts code input := by
  constructor
  · intro derivation
    exact (CommonRoleRegularHalting.machine_halts_exact code input).mp
      (reflect code derivation (CommonRoleRegularHalting.start code input) (clock (count code)).eval rfl
        (Common.equivalent_refl _))
  · intro halting
    obtain ⟨dictionary⟩ := (CommonRoleFiniteTailHalting.dictionary_exact code input).mpr halting
    exact forget _ dictionary

theorem guarded_iff_arbitrary_common (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (Dictionary (visible code) (CommonRoleFiniteTailHalting.startGoal code input)) ↔
      CommonRoleFiniteShadowSemantic.Derives (visible code) (meaning (CommonRoleFiniteTailHalting.startGoal code input)) :=
  (CommonRoleFiniteTailHalting.dictionary_exact code input).trans (arbitrary_common_exact code input).symm

end Yulang.CommonRoleFiniteTailSemantic
