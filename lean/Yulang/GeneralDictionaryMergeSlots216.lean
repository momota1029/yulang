import Yulang.GeneralNominalMergeResidual178
import Yulang.GeneralNominalCenteredModelExtension
import Yulang.GeneralNominalAllocationSupport

/-! Patch exactly the non-singleton aggregate endpoints. Separation from live
support is explicit; this does not assert that an installed aggregate is free. -/
namespace Yulang.GeneralDictionaryMergeSlots216
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension
open CommonNominalFullCarrier

noncomputable def active (declaration : Declaration) (bindings : Bindings) : List Nat :=
  declaration.inputNames.filter fun name => (occurrences bindings name).length != 1

def slot (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (purpose name : Nat) : Nat :=
  source state registry invocation (origin invocation declaration.id purpose name 0)

theorem slot_injective (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (a b x y : Nat)
    (equal : slot state registry invocation declaration a x = slot state registry invocation declaration b y) :
    a = b ∧ x = y := by
  have same := (GeneralNominalIdentities.source_identity state.seed _ _).mp equal
  exact ⟨congrArg (fun key : Origin => key.2.2.1) same,congrArg (fun key : Origin => key.2.2.2.1) same⟩

noncomputable def names (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (purpose : Nat) : Fin (active declaration bindings).length → Nat :=
  fun i => slot state registry invocation declaration purpose (active declaration bindings)[i]

noncomputable def values (previous : Assignment) (declaration : Declaration) (bindings : Bindings)
    (upperSide : Bool) : Fin (active declaration bindings).length → Ty :=
  fun i => (if upperSide then upper (occurrences bindings (active declaration bindings)[i])
    else lower (occurrences bindings (active declaration bindings)[i])).eval CommonNominalFullCarrier.model previous

noncomputable def patch (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (previous : Assignment) : Assignment :=
  assign (assign previous (names state registry invocation declaration bindings 0) (values previous declaration bindings false))
    (names state registry invocation declaration bindings 1) (values previous declaration bindings true)

theorem coherent (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (previous : Assignment) (purpose : Nat) (upperSide : Bool) :
    ∀ i j, names state registry invocation declaration bindings purpose i = names state registry invocation declaration bindings purpose j →
      values previous declaration bindings upperSide i = values previous declaration bindings upperSide j := by
  intro i j equal
  have same := (slot_injective state registry invocation declaration purpose purpose _ _ equal).2
  simp only [values,same]
  rfl

theorem sides_separate (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (i j : Fin (active declaration bindings).length) :
    names state registry invocation declaration bindings 0 i ≠ names state registry invocation declaration bindings 1 j := by
  intro equal
  have impossible := (slot_injective state registry invocation declaration 0 1 _ _ equal).1
  cases impossible

theorem patch_outside (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (previous : Assignment) (name : Nat)
    (low : ∀ i, names state registry invocation declaration bindings 0 i ≠ name)
    (high : ∀ i, names state registry invocation declaration bindings 1 i ≠ name) :
    patch state registry invocation declaration bindings previous name = previous name := by
  unfold patch
  rw [assign_outside _ _ _ high,assign_outside _ _ _ low]

theorem patch_lower (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (previous : Assignment) (i : Fin (active declaration bindings).length) :
    (patch state registry invocation declaration bindings previous (names state registry invocation declaration bindings 0 i)).1 =
      values previous declaration bindings false i := by
  unfold patch
  rw [assign_outside _ _ _ (fun j => (sides_separate state registry invocation declaration bindings i j).symm)]
  exact assign_value previous _ _ (coherent state registry invocation declaration bindings previous 0 false) i

theorem patch_upper (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (previous : Assignment) (i : Fin (active declaration bindings).length) :
    (patch state registry invocation declaration bindings previous (names state registry invocation declaration bindings 1 i)).1 =
      values previous declaration bindings true i :=
  assign_value _ _ _ (coherent state registry invocation declaration bindings previous 1 true) i

end Yulang.GeneralDictionaryMergeSlots216
