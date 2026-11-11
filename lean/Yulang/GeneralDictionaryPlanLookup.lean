import Yulang.GeneralDictionaryEmissionPlans

/-!
# Executable exact lookup of checked dictionary emission plans

This finite registry lookup returns the complete canonical child list of one
visible implementation key and root role under a fixed resolved frame. Exactness
is against the independent Plan relation, not a full candidate or resolver.
-/
namespace Yulang.GeneralDictionaryPlanLookup
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryEmissionPlans

def lookup (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) : Option (List (Occurrence registry.roles)) :=
  (registry.declarations.attach.find? (fun declaration =>
    declaration.val.id == key && declaration.val.role == root.demand.role)).map
      (fun declaration => children frame root declaration.val (checked.2 declaration.val declaration.property))

/-- No feasibility, success or model premise. The fixed frame remains explicit. -/
theorem lookup_exact (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) (demands : List (Occurrence registry.roles)) :
    lookup registry checked frame root key = some demands ↔ Plan registry checked frame root key demands := by
  unfold lookup
  cases found : registry.declarations.attach.find? (fun declaration =>
      declaration.val.id == key && declaration.val.role == root.demand.role) with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨declaration, present, identity, role, _⟩
        have absent := (List.find?_eq_none.mp found) ⟨declaration, present⟩ (by simp)
        simp only [identity, role, beq_self_eq_true, Bool.and_self, not_true_eq_false] at absent
  | some declaration =>
      have conditions := List.find?_some found
      have keys : declaration.val.id = key ∧ declaration.val.role = root.demand.role := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using conditions
      have plan : Plan registry checked frame root key
          (children frame root declaration.val (checked.2 declaration.val declaration.property)) :=
        ⟨declaration.val, declaration.property, keys.1, keys.2, rfl⟩
      constructor
      · intro same
        have values := Option.some.inj same
        rw [← values]
        exact plan
      · intro given
        have same := plan_children_functional registry checked frame root key _ _ plan given
        exact congrArg some same

/-- Failure means precisely that no independent matching declaration plan exists,
not that a role application is semantically rejected. -/
theorem lookup_none (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) :
    lookup registry checked frame root key = none ↔
      ∀ demands, ¬ Plan registry checked frame root key demands := by
  constructor
  · intro empty demands plan
    have found := (lookup_exact registry checked frame root key demands).mpr plan
    rw [empty] at found
    cases found
  · intro empty
    cases found : lookup registry checked frame root key with
    | none => rfl
    | some demands => exact False.elim (empty demands ((lookup_exact registry checked frame root key demands).mp found))

/-- Visible and where reordering changes neither executable child payload nor
source identity at a fixed frame. This is not final-state resolver invariance. -/
theorem lookup_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat) :
    lookup ⟨constructors, roles, first⟩ one frame root key =
      lookup ⟨constructors, roles, last⟩ two frame root key := by
  cases found : lookup ⟨constructors, roles, first⟩ one frame root key with
  | none =>
      have empty := (lookup_none _ one frame root key).mp found
      have other : lookup ⟨constructors, roles, last⟩ two frame root key = none := by
        apply (lookup_none _ two frame root key).mpr
        intro demands plan
        exact empty demands ((plan_reorders_iff constructors roles first last one two order frame root key demands).mpr plan)
      exact other.symm
  | some demands =>
      have plan := (lookup_exact _ one frame root key demands).mp found
      have otherPlan := (plan_reorders_iff constructors roles first last one two order frame root key demands).mp plan
      exact ((lookup_exact _ two frame root key demands).mpr otherPlan).symm

end Yulang.GeneralDictionaryPlanLookup
