import Yulang.GeneralDictionaryAgreedRoleExamples174

/-! Executable bounded-height search with an independently checked certificate.
Fuel limits certificate search, not language evaluation. A false result does
not reject a registry. Completeness is proved for exactly the role-stratified
fragment, not for general Paterson-recursive declarations. -/
namespace Yulang.GeneralDictionaryAgreedComputed174
open GeneralDeclarations GeneralDictionaryAgreedEdge174
open GeneralNominalSupport GeneralSourceDictionaries GeneralNominalActualAgreedLocal
open CommonRoleOutermostResolver (Child)

/-- Actual declared child-role edges, including all declarations at this role. -/
def childRoles (registry : Registry) (role : Nat) : List Nat :=
  registry.declarations.flatMap fun declaration =>
    if declaration.role = role then declaration.requirements.map (·.role) else []

/-- Maximum length of a declared role path truncated at `fuel`. -/
def computedHeight (registry : Registry) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, role =>
    (childRoles registry role).foldl
      (fun height child => max height (computedHeight registry fuel child + 1)) 0

/-- Verify every actual declared edge against the computed candidate rank. -/
def check (registry : Registry) (fuel : Nat) : Bool :=
  registry.declarations.all fun declaration => declaration.requirements.all fun clause =>
    decide (computedHeight registry fuel clause.role < computedHeight registry fuel declaration.role)

theorem check_iff (registry : Registry) (fuel : Nat) :
    check registry fuel = true ↔ RoleStratified registry (computedHeight registry fuel) := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, RoleStratified]

theorem check_sound (passed : check registry fuel = true) :
    RoleStratified registry (computedHeight registry fuel) :=
  (check_iff registry fuel).mp passed

theorem checked_whereAccessible {roles : Roles.RoleDecls}
    (passed : check registry fuel = true) (defer : Bool) (gap : GapPredicate roles)
    (state : Tracked roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local
      (GeneralNominalActualAgreedBoundary.boundary defer gap).toSourceBoundary registry state)) root :=
  boundary_whereAccessible (check_sound passed) root

/-- The executable edge list contains exactly the declared requirements at a role. -/
theorem mem_childRoles : child ∈ childRoles registry role ↔
    ∃ declaration ∈ registry.declarations, declaration.role = role ∧
      ∃ clause ∈ declaration.requirements, clause.role = child := by
  simp only [childRoles, List.mem_flatMap]
  constructor
  · rintro ⟨declaration, visible, present⟩
    split at present
    next same =>
      obtain ⟨clause, member, eq⟩ := List.mem_map.mp present
      exact ⟨declaration, visible, same, clause, member, eq⟩
    next => simp at present
  · rintro ⟨declaration, visible, same, clause, member, eq⟩
    refine ⟨declaration, visible, ?_⟩
    simp only [same, ↓reduceIte]
    exact List.mem_map.mpr ⟨clause, member, eq⟩

theorem child_rank_lt (stratified : RoleStratified registry rank)
    (present : child ∈ childRoles registry role) : rank child < rank role := by
  obtain ⟨declaration, visible, same, clause, member, eq⟩ := mem_childRoles.mp present
  rw [← same, ← eq]
  exact stratified declaration visible clause member

private theorem fold_congr (xs : List Nat) (f g : Nat → Nat)
    (same : ∀ x ∈ xs, f x = g x) (initial : Nat) :
    xs.foldl (fun h x => max h (f x)) initial =
      xs.foldl (fun h x => max h (g x)) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (by simp)]
    exact ih (fun y mem => same y (by simp [mem])) _

private theorem initial_le_fold (xs : List Nat) (f : Nat → Nat) (initial : Nat) :
    initial ≤ xs.foldl (fun h x => max h (f x)) initial := by
  induction xs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem member_le_fold (xs : List Nat) (f : Nat → Nat) (initial : Nat)
    (present : child ∈ xs) : f child ≤ xs.foldl (fun h x => max h (f x)) initial := by
  induction xs generalizing initial with
  | nil => cases present
  | cons x xs ih =>
    rcases List.mem_cons.mp present with same | member
    · subst child
      exact Nat.le_trans (Nat.le_max_right _ _) (initial_le_fold xs f _)
    · exact ih _ member

/-- Once fuel reaches a declaration-level rank, all further heights agree.
The rank is used only in this completeness proof, not by the executable checker. -/
theorem height_stabilizes (stratified : RoleStratified registry rank) (role : Nat) :
    ∀ a b, rank role ≤ a → rank role ≤ b →
      computedHeight registry a role = computedHeight registry b role := by
  induction role using (measure rank).wf.induction with
  | h role ih =>
    intro a b ha hb
    have zero_empty (zero : rank role = 0) : childRoles registry role = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child present
      have lt := child_rank_lt stratified present
      omega
    cases a with
    | zero =>
      have empty := zero_empty (by omega)
      cases b with
      | zero => rfl
      | succ b => simp [computedHeight, empty]
    | succ a =>
      cases b with
      | zero =>
        have empty := zero_empty (by omega)
        simp [computedHeight, empty]
      | succ b =>
        apply fold_congr
        intro child present
        have lt := child_rank_lt stratified present
        have eq := ih child lt a b (by omega) (by omega)
        exact congrArg (· + 1) eq

/-- A finite sufficient-fuel criterion; no hand-supplied rank is needed to
execute `check`, but existence of a declaration rank proves its completeness. -/
theorem check_complete (stratified : RoleStratified registry rank)
    (large : ∀ declaration ∈ registry.declarations, rank declaration.role ≤ fuel) :
    check registry fuel = true := by
  apply (check_iff registry fuel).mpr
  intro declaration visible clause present
  have edge : clause.role ∈ childRoles registry declaration.role :=
    mem_childRoles.mpr ⟨declaration, visible, rfl, clause, present, rfl⟩
  have upper := member_le_fold (childRoles registry declaration.role)
    (fun child => computedHeight registry fuel child + 1) 0 edge
  have stable := height_stabilizes stratified declaration.role fuel (fuel + 1)
    (large declaration visible) (by have h := large declaration visible; omega)
  change computedHeight registry fuel clause.role + 1 ≤
    computedHeight registry (fuel + 1) declaration.role at upper
  rw [← stable] at upper
  omega

/-- A rank is finite on the finite declaration list; this bound is for the
completeness theorem, not an input to `computedHeight` or `check`. -/
def rankBudget (registry : Registry) (rank : Nat → Nat) : Nat :=
  (registry.declarations.map (fun declaration => rank declaration.role)).foldl max 0

theorem check_complete_budget (stratified : RoleStratified registry rank) :
    check registry (rankBudget registry rank) = true := by
  apply check_complete stratified
  intro declaration visible
  have present : rank declaration.role ∈ registry.declarations.map (fun d => rank d.role) :=
    List.mem_map.mpr ⟨declaration, visible, rfl⟩
  exact member_le_fold _ (fun n => n) 0 present

theorem exists_check_iff : (∃ fuel, check registry fuel = true) ↔
    ∃ rank, RoleStratified registry rank := by
  constructor
  · rintro ⟨fuel, passed⟩
    exact ⟨computedHeight registry fuel, check_sound passed⟩
  · rintro ⟨rank, stratified⟩
    exact ⟨rankBudget registry rank, check_complete_budget stratified⟩

theorem check_of_leaves (leaves : ∀ declaration ∈ registry.declarations,
    declaration.requirements = []) (fuel : Nat) : check registry fuel = true := by
  apply (check_iff registry fuel).mpr
  intro declaration visible clause present
  rw [leaves declaration visible] at present
  cases present

/-- Zero fuel can fail even for a checked nonleaf DAG. -/
theorem wrap_zero_false : check GeneralDictionaryAgreedRoleExamples174.wrapOnly 0 = false := by
  decide +kernel

theorem wrap_computed : check GeneralDictionaryAgreedRoleExamples174.wrapOnly 1 = true := by
  decide +kernel

theorem display_fails (fuel : Nat) : check GeneralDeclarationExamples.registry fuel = false := by
  cases result : check GeneralDeclarationExamples.registry fuel with
  | false => rfl
  | true => exact False.elim (GeneralDictionaryAgreedRoleExamples174.display_not_stratified _ (check_sound result))

end Yulang.GeneralDictionaryAgreedComputed174
