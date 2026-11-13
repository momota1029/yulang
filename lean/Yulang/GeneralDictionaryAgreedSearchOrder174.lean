import Yulang.GeneralDictionaryAgreedComputed174

/-! Declaration and where-clause reordering preserve executable certificate
search exactly at every fuel. This is search-order independence only, NOT
canonicalLocalOrder for different final saturated states. -/
namespace Yulang.GeneralDictionaryAgreedSearchOrder174
open GeneralDeclarations GeneralRegistryReordering
open GeneralDictionaryAgreedEdge174 GeneralDictionaryAgreedComputed174

/-- The declared child-role relation is independent of both source enumerations. -/
theorem childRoles_mem_iff (order : Reorders first last) :
    child ∈ childRoles first role ↔ child ∈ childRoles last role := by
  constructor
  · intro present
    obtain ⟨declaration, visible, roleEq, clause, member, childEq⟩ := mem_childRoles.mp present
    obtain ⟨other, visible', changed⟩ := reorders_visible order declaration visible
    exact mem_childRoles.mpr ⟨other, visible', changed.role.symm.trans roleEq,
      clause, changed.requirements.mem_iff.mp member, childEq⟩
  · intro present
    obtain ⟨declaration, visible, roleEq, clause, member, childEq⟩ := mem_childRoles.mp present
    obtain ⟨other, visible', changed⟩ := reorders_visible_back order declaration visible
    exact mem_childRoles.mpr ⟨other, visible', changed.role.trans roleEq,
      clause, changed.requirements.mem_iff.mpr member, childEq⟩

/-- Characterize a maximum fold by its initial value and member values. -/
theorem fold_max_le_iff (xs : List Nat) (f : Nat → Nat) (initial bound : Nat) :
    xs.foldl (fun h x => max h (f x)) initial ≤ bound ↔
      initial ≤ bound ∧ ∀ x ∈ xs, f x ≤ bound := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨head, tail⟩
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) head, ?_⟩
      intro y present
      rcases List.mem_cons.mp present with same | member
      · subst y
        exact Nat.le_trans (Nat.le_max_right _ _) head
      · exact tail y member
    · rintro ⟨initialLe, values⟩
      exact ⟨Nat.max_le.mpr ⟨initialLe, values x (by simp)⟩,
        fun y member => values y (List.mem_cons_of_mem _ member)⟩

/-- Equal membership and equal value functions suffice; multiplicity does not
matter for max, without assuming a stronger permutation witness. -/
theorem fold_max_eq (xs ys : List Nat) (f g : Nat → Nat)
    (members : ∀ x, x ∈ xs ↔ x ∈ ys) (values : ∀ x ∈ xs, f x = g x)
    (initial : Nat) :
    xs.foldl (fun h x => max h (f x)) initial =
      ys.foldl (fun h x => max h (g x)) initial := by
  apply Nat.le_antisymm
  · have bounds := (fold_max_le_iff ys g initial _).mp (Nat.le_refl _)
    apply (fold_max_le_iff xs f initial _).mpr
    exact ⟨bounds.1, fun x member => (values x member) ▸ bounds.2 x ((members x).mp member)⟩
  · have bounds := (fold_max_le_iff xs f initial _).mp (Nat.le_refl _)
    apply (fold_max_le_iff ys g initial _).mpr
    refine ⟨bounds.1, ?_⟩
    intro x member
    have old := (members x).mpr member
    rw [← values x old]
    exact bounds.2 x old

/-- Every finite-fuel computed role height is exactly invariant. -/
theorem computedHeight_reorders (order : Reorders first last) (fuel role : Nat) :
    computedHeight first fuel role = computedHeight last fuel role := by
  induction fuel generalizing role with
  | zero => rfl
  | succ fuel ih =>
    apply fold_max_eq
    · intro child
      exact childRoles_mem_iff order
    · intro child _
      exact congrArg (· + 1) (ih child)

theorem stratified_reorders_iff (order : Reorders first last) (rank : Nat → Nat) :
    RoleStratified first rank ↔ RoleStratified last rank := by
  constructor
  · exact stratified_reorders order
  · intro stratified declaration visible clause member
    obtain ⟨other, visible', changed⟩ := reorders_visible order declaration visible
    rw [changed.role]
    exact stratified other visible' clause (changed.requirements.mem_iff.mp member)

/-- Pass/fail of the executable checker is unchanged at the same fuel,
including fuel insufficient to certify the role DAG. -/
theorem check_reorders (order : Reorders first last) (fuel : Nat) :
    check first fuel = check last fuel := by
  have ranks : computedHeight first fuel = computedHeight last fuel :=
    funext (computedHeight_reorders order fuel)
  have truth : check first fuel = true ↔ check last fuel = true := by
    rw [check_iff, check_iff, ranks]
    exact stratified_reorders_iff order _
  cases hfirst : check first fuel <;> cases hlast : check last fuel <;> simp_all

/-- The sufficient completeness budget is also enumeration-independent. -/
theorem rankBudget_reorders (order : Reorders first last) (rank : Nat → Nat) :
    rankBudget first rank = rankBudget last rank := by
  apply fold_max_eq _ _ (fun n => n) (fun n => n)
  · intro value
    constructor
    · intro member
      obtain ⟨declaration, visible, eq⟩ := List.mem_map.mp member
      obtain ⟨other, visible', changed⟩ := reorders_visible order declaration visible
      exact List.mem_map.mpr ⟨other, visible', by rw [← changed.role]; exact eq⟩
    · intro member
      obtain ⟨declaration, visible, eq⟩ := List.mem_map.mp member
      obtain ⟨other, visible', changed⟩ := reorders_visible_back order declaration visible
      exact List.mem_map.mpr ⟨other, visible', by rw [changed.role]; exact eq⟩
  · intros; rfl

abbrev reversedExample : Registry :=
  ⟨GeneralDeclarationExamples.constructors, GeneralDeclarationExamples.roles,
    [GeneralDeclarationExamples.wrap, GeneralDeclarationExamples.display]⟩

theorem example_reorders : Reorders GeneralDeclarationExamples.registry reversedExample := by
  refine ⟨rfl, rfl, reversedExample.declarations, ?_, ?_⟩
  · exact List.Perm.swap _ _ []
  · exact .cons (declarationReorders_refl _) (.cons (declarationReorders_refl _) .nil)

theorem reversedExample_checked : Checked reversedExample :=
  reorders_checked example_reorders GeneralDeclarationExamples.registry_checked

/-- The same-role legal recursion keeps growing with search fuel on either
ordering; its failed role-DAG certificate is not language rejection. -/
theorem recursive_example_height :
    computedHeight GeneralDeclarationExamples.registry 3 0 = 3 ∧
      computedHeight reversedExample 3 0 = 3 := by
  constructor <;> decide +kernel

theorem recursive_example_check (fuel : Nat) : check reversedExample fuel = false := by
  rw [← check_reorders example_reorders fuel]
  exact display_fails fuel

end Yulang.GeneralDictionaryAgreedSearchOrder174
