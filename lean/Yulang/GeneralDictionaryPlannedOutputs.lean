import Yulang.GeneralDictionaryAssociatedProvenance
import Yulang.GeneralDictionaryPlanLookup

/-!
# Actual declaration-key plans with complete associated-body provenance

The same checked visible declaration produces both canonical child obligations
and every root associated RHS. This joins two formerly separate lookups without
interpreting nominal patterns or positional defaults as ordinary Common terms.
-/
namespace Yulang.GeneralDictionaryPlannedOutputs
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryEmissionPlans
open GeneralDictionaryAssociatedProvenance (Body Supplies outputs)
open GeneralSourceState (Output)

abbrev Result (roles : Roles.RoleDecls) := List (Occurrence roles) × List (Output × Option Body)

def OutputPlan (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) (result : Result registry.roles) : Prop :=
  ∃ declaration, ∃ present : declaration ∈ registry.declarations,
    declaration.id = key ∧ declaration.role = root.demand.role ∧
      result = (children frame root declaration (checked.2 declaration present),
        outputs registry.roles declaration root.demand)

theorem output_plan_functional (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (first last : Result registry.roles)
    (one : OutputPlan registry checked frame root key first)
    (two : OutputPlan registry checked frame root key last) : first = last := by
  obtain ⟨a, ha, ka, _, ea⟩ := one
  obtain ⟨b, hb, kb, _, eb⟩ := two
  have same := declaration_key_unique registry checked a b ha hb (ka.trans kb.symm)
  subst b
  exact ea.trans eb.symm

def lookup (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) : Option (Result registry.roles) :=
  (registry.declarations.attach.find? (fun declaration =>
    declaration.val.id == key && declaration.val.role == root.demand.role)).map
      (fun declaration =>
        (children frame root declaration.val (checked.2 declaration.val declaration.property),
          outputs registry.roles declaration.val root.demand))

theorem lookup_exact (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (key : Nat) (result : Result registry.roles) :
    lookup registry checked frame root key = some result ↔ OutputPlan registry checked frame root key result := by
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
      have keys : declaration.val.id = key ∧ declaration.val.role = root.demand.role := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some found
      have plan : OutputPlan registry checked frame root key
          (children frame root declaration.val (checked.2 declaration.val declaration.property),
            outputs registry.roles declaration.val root.demand) :=
        ⟨declaration.val, declaration.property, keys.1, keys.2, rfl⟩
      constructor
      · intro same
        rw [← Option.some.inj same]
        exact plan
      · intro given
        exact congrArg some (output_plan_functional registry checked frame root key _ _ plan given)

/-- The new result preserves precisely the old complete canonical child plan. -/
theorem output_plan_children (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (result : Result registry.roles) (plan : OutputPlan registry checked frame root key result) :
    Plan registry checked frame root key result.1 := by
  obtain ⟨declaration, present, identity, role, rfl⟩ := plan
  exact ⟨declaration, present, identity, role, rfl⟩

/-- All repeated output source occurrences survive, not just their distinct names. -/
theorem output_plan_sources (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (result : Result registry.roles) (plan : OutputPlan registry checked frame root key result) :
    result.2.map Prod.fst = root.demand.outputs := by
  obtain ⟨declaration, _, _, _, rfl⟩ := plan
  exact GeneralDictionaryAssociatedProvenance.outputs_sources registry.roles declaration root.demand

/-- Every declared obligation has an explicit/default body from the exact same
visible declaration that supplies its child plan. This is not term evaluation. -/
theorem output_plan_covered (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (result : Result registry.roles) (plan : OutputPlan registry checked frame root key result)
    (output : Output) (present : output ∈ root.demand.outputs) :
    ∃ body, (output, some body) ∈ result.2 := by
  obtain ⟨declaration, visible, _, role, rfl⟩ := plan
  obtain ⟨body, member, _⟩ := GeneralDictionaryAssociatedProvenance.outputs_complete
    registry declaration (checked.2 declaration visible) root.demand role output present
  exact ⟨body, member⟩

end Yulang.GeneralDictionaryPlannedOutputs
