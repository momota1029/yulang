import Yulang.GeneralRebaseCompiledStep282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledQuery282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAssignmentCongruence238 (Same subtype_iff)
open GeneralRebaseHistoryOrder282 (history decode compatible)
open GeneralRebaseProspective282 (Compiled decoded compile_old)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalDemandMerging (SameOrigin Related)
open GeneralNominalDemandMerging (All₂)
open CommonNominalFullCarrier (Equivalent model)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {state : State roles}

def Denoted (state : State roles) (m : Assignment) : Prop :=
  ∃ base, Compiled state base ∧ m = decode state base

theorem compare {pred : Assignment → Prop} (reach : Reachable r root state)
    (stable : ∀ x y, Same x y → (pred x ↔ pred y)) :
    (∀ a, Models state a → pred a) ↔ ∀ b, Denoted state b → pred b := by
  have empty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach
  have records := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  constructor
  · rintro enough _ ⟨base,supported,rfl⟩
    exact enough _ ((decoded empty base).mp supported)
  · intro all original valid
    apply (stable _ _ (compatible reach valid)).mp
    exact all _ ⟨original,compile_old records empty original valid,rfl⟩

theorem mapped_type (state : State roles) (m : Assignment) (n : Nat) :
    (GeneralPresenceOrderedSubstitution247.mapping (history state) n).ty.eval model m =
      (decode state m n).1 :=
  congrArg Prod.fst (GeneralPresenceOrderedSubstitution247.mapping_eval (history state) model m n)

theorem equality (reach : Reachable r root state) (x y : Nat) :
    GeneralNominalVersionedMixedKernel234.Equal state x y ↔
      ∀ m, Compiled state m →
        Equivalent ((GeneralPresenceOrderedSubstitution247.mapping (history state) x).ty.eval model m)
          ((GeneralPresenceOrderedSubstitution247.mapping (history state) y).ty.eval model m) := by
  have law := compare (pred := fun a => Equivalent (a x).1 (a y).1) reach
    (fun _ _ same => and_congr (subtype_iff (same x).1 (same y).1) (subtype_iff (same y).1 (same x).1))
  apply law.trans
  constructor
  · intro every m compiled
    have raw := every (decode state m) ⟨m,compiled,rfl⟩
    rw [mapped_type state m x,mapped_type state m y]
    exact raw
  · rintro every a ⟨m,compiled,rfl⟩
    have old := every m compiled
    rwa [mapped_type state m x,mapped_type state m y] at old

theorem all₂_equiv {α β : Type} {p q : α → β → Prop}
    (same : ∀ x y, p x y ↔ q x y) (xs : List α) (ys : List β) :
    All₂ p xs ys ↔ All₂ q xs ys := by
  constructor
  · intro evidence
    induction evidence with
    | nil => exact .nil
    | cons first rest ih => exact .cons ((same _ _).mp first) ih
  · intro evidence
    induction evidence with
    | nil => exact .nil
    | cons first rest ih => exact .cons ((same _ _).mpr first) ih

theorem same_origin (reach : Reachable r root state) (a b : Origin) :
    SameOrigin (Models state) a b ↔ SameOrigin (Denoted state) a b :=
  compare (pred := fun m => GeneralNominalOriginTerms.Same m a b) reach
    (fun _ _ same => GeneralNominalOriginCongruence238.shared_iff same a b)

theorem same_inputs (reach : Reachable r root state) (a b : Site roles) :
    SameInputs (Models state) a b ↔ SameInputs (Denoted state) a b := by
  unfold SameInputs GeneralNominalDemandMerging.SameInputs
  apply and_congr Iff.rfl
  apply all₂_equiv
  intro left right
  unfold Related
  exact exists_congr fun l => exists_congr fun r =>
    and_congr Iff.rfl (and_congr Iff.rfl (same_origin reach l r))

end Yulang.GeneralRebaseCompiledQuery282
