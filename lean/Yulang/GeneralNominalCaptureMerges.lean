import Yulang.GeneralNominalEmissionOrigins

/-! Actual values of repeated captures remain inside the computed merged
interval used by every variable where input. The allocation is the existing
invocation-based allocation; no representative type is allocated. -/
namespace Yulang.GeneralNominalCaptureMerges

open GeneralNominalAllocation
open GeneralSourceState (Interval)
open GeneralDeclarations
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open PresenceNormalForm (All Atom)

def Fits (model : GeneralNominalCommonBridge.Assignment) (bounds : Interval) (actual : Ty) : Prop :=
  Subtype (model bounds.1).1 actual ∧ Subtype actual (model bounds.2).1

theorem lower_exact (model : GeneralNominalCommonBridge.Assignment) (bounds : List Interval)
    (nonempty : bounds ≠ []) (actual : Ty) :
    Subtype ((lower bounds).eval CommonNominalFullCarrier.model model) actual ↔
      ∀ pair ∈ bounds, Subtype (model pair.1).1 actual := by
  induction bounds with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil => simp [lower,TyTerm.eval]
      | cons next rest =>
          change Subtype (.union (model head.1).1 ((lower (next :: rest)).eval CommonNominalFullCarrier.model model)) actual ↔ _
          exact (common_union_is_join (model head.1).1
            ((lower (next :: rest)).eval CommonNominalFullCarrier.model model) actual).trans (by
              rw [ih (by simp)]
              simp)

theorem upper_exact (model : GeneralNominalCommonBridge.Assignment) (bounds : List Interval)
    (nonempty : bounds ≠ []) (actual : Ty) :
    Subtype actual ((upper bounds).eval CommonNominalFullCarrier.model model) ↔
      ∀ pair ∈ bounds, Subtype actual (model pair.2).1 := by
  induction bounds with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil => simp [upper,TyTerm.eval]
      | cons next rest =>
          change Subtype actual (.inter (model head.2).1 ((upper (next :: rest)).eval CommonNominalFullCarrier.model model)) ↔ _
          exact (common_inter_is_meet (model head.2).1
            ((upper (next :: rest)).eval CommonNominalFullCarrier.model model) actual).trans (by
              rw [ih (by simp)]
              simp)

theorem equations_exact (model : GeneralNominalCommonBridge.Assignment) (source : Nat) (term : TyTerm Nat) :
    All CommonNominalFullCarrier.model model (equations source term) ↔
      Equivalent (model source).1 (term.eval CommonNominalFullCarrier.model model) := by
  simp [equations,All,Atom.Holds,TyTerm.eval,CommonNominalFullCarrier.model,Equivalent]

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

theorem repeated_child_correspondence (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models (propagate state registry invocation declaration bindings) model)
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : occurrences bindings name ≠ []) (actual : Ty)
    (clause : Clause) (valid : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (pattern : GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name) :
    let child := GeneralDeclarationDemands.childDemand declaration clause valid
      (capture state registry invocation declaration.id bindings)
      (allocation state registry invocation declaration.id clause)
    Fits model (child.arguments index) actual ↔ ∀ bounds ∈ occurrences bindings name, Fits model bounds actual := by
  dsimp only
  simpa only [GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,pattern] using
    propagated_capture_exact state registry invocation declaration bindings model models name declared nonempty actual

end Yulang.GeneralNominalCaptureMerges
