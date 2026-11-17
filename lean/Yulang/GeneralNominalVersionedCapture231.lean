import Yulang.GeneralNominalVersionedAllocation231
namespace Yulang.GeneralNominalVersionedCapture231
open GeneralNominalAllocation (Bindings occurrences lower upper equations)
open GeneralNominalVersionedAllocation231
open GeneralNominalCaptureMerges (Fits lower_exact upper_exact equations_exact)
open GeneralSourceState (Interval)
open GeneralDeclarations
open CommonNominalFullCarrier
open PresenceNormalForm (All Atom)

theorem capture_interval_exact (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment)
    (recorded : All CommonNominalFullCarrier.model model (merges state registry invocation declaration bindings))
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : occurrences bindings name ≠ []) (actual : Ty) :
    Fits model ((capture state registry invocation declaration.id bindings).inputs name) actual ↔
      ∀ bounds ∈ occurrences bindings name, Fits model bounds actual := by
  cases observed : occurrences bindings name with
  | nil => exact False.elim (nonempty observed)
  | cons first rest =>
      cases rest with
      | nil => simp [capture,observed]
      | cons second tail =>
          have generated : All CommonNominalFullCarrier.model model
              (equations ((capture state registry invocation declaration.id bindings).inputs name).1 (lower (first :: second :: tail)) ++
                equations ((capture state registry invocation declaration.id bindings).inputs name).2 (upper (first :: second :: tail))) := by
            intro atom member
            apply recorded atom
            apply List.mem_flatMap.mpr
            exact ⟨name,declared,by simpa [observed] using member⟩
          have split := (PresenceNormalForm.all_append ..).mp generated
          have lo := (equations_exact ..).mp split.1
          have hi := (equations_exact ..).mp split.2
          have lowerBounds := lower_exact model (first :: second :: tail) (by simp) actual
          have upperBounds := upper_exact model (first :: second :: tail) (by simp) actual
          constructor
          · intro fits bounds member
            exact ⟨lowerBounds.mp (subtype_trans lo.2 fits.1) bounds member,
              upperBounds.mp (subtype_trans fits.2 hi.1) bounds member⟩
          · intro fits
            exact ⟨subtype_trans lo.1 (lowerBounds.mpr (fun pair member => (fits pair member).1)),
              subtype_trans (upperBounds.mpr (fun pair member => (fits pair member).2)) hi.2⟩

theorem propagated_capture_exact (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models (propagate state registry invocation declaration bindings) model)
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : occurrences bindings name ≠ []) (actual : Ty) :
    Fits model ((capture state registry invocation declaration.id bindings).inputs name) actual ↔
      ∀ bounds ∈ occurrences bindings name, Fits model bounds actual :=
  capture_interval_exact state registry invocation declaration bindings model
    ((propagate_models ..).mp models).2.2 name declared nonempty actual


/-- Actual argument centers keep their old names: versioning only changes the
aggregate bounds consumed by the Fits judgment above. -/
theorem capture_registry_independent (state : GeneralNominalState.State) (a b : Registry)
    (root declaration : Nat) (bindings : Bindings) :
    capture state a root declaration bindings = capture state b root declaration bindings := rfl

theorem capture_extend (state : GeneralNominalState.State) (registry : Registry)
    (root declaration : Nat) (bindings : Bindings) (reserved atoms) :
    capture (GeneralNominalState.extend state reserved atoms) registry root declaration bindings =
      capture state registry root declaration bindings := rfl

end Yulang.GeneralNominalVersionedCapture231
