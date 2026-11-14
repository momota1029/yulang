import Yulang.GeneralNominalCaptureMerges

/-! Exact same-assignment obligations for every allocated capture extremum.
These equalities are not inferred from cross compatibility or the existence of
another branch model. Zero and repeated occurrences are retained. -/
namespace Yulang.GeneralNominalMergeResidual178
open GeneralNominalAllocation GeneralDeclarations CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

/-- Singleton occurrences allocate no merge equations. All other cardinalities
require both allocated endpoints to denote the computed extrema. -/
def CaptureExtrema (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ name ∈ declaration.inputNames, ∀ bounds,
    occurrences bindings name = bounds → (∀ pair, bounds ≠ [pair]) →
    Equivalent (model ((capture state registry invocation declaration.id bindings).inputs name).1).1
      ((lower bounds).eval CommonNominalFullCarrier.model model) ∧
    Equivalent (model ((capture state registry invocation declaration.id bindings).inputs name).2).1
      ((upper bounds).eval CommonNominalFullCarrier.model model)

theorem merges_iff_extrema (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration bindings) ↔
    CaptureExtrema state registry invocation declaration bindings model := by
  constructor
  · intro valid name declared bounds observed nonsingle
    have localValid : PresenceNormalForm.All CommonNominalFullCarrier.model model
        (equations ((capture state registry invocation declaration.id bindings).inputs name).1 (lower bounds) ++
         equations ((capture state registry invocation declaration.id bindings).inputs name).2 (upper bounds)) := by
      intro atom member
      apply valid atom
      apply List.mem_flatMap.mpr
      refine ⟨name,declared,?_⟩
      rw [observed]
      split
      · exact False.elim (nonsingle _ rfl)
      · exact member
    have parts := (PresenceNormalForm.all_append ..).mp localValid
    exact ⟨(GeneralNominalCaptureMerges.equations_exact ..).mp parts.1,
      (GeneralNominalCaptureMerges.equations_exact ..).mp parts.2⟩
  · intro valid atom member
    obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp member
    cases observed : occurrences bindings name with
    | nil =>
      have parts := valid name declared [] observed (by intro pair; simp)
      have both := (PresenceNormalForm.all_append ..).mpr
        ⟨(GeneralNominalCaptureMerges.equations_exact ..).mpr parts.1,
         (GeneralNominalCaptureMerges.equations_exact ..).mpr parts.2⟩
      exact both atom (by simpa only [observed] using member)
    | cons first rest =>
      cases rest with
      | nil => simp only [observed,List.not_mem_nil] at member
      | cons second tail =>
        have parts := valid name declared (first :: second :: tail) observed (by intro pair; simp)
        have both := (PresenceNormalForm.all_append ..).mpr
          ⟨(GeneralNominalCaptureMerges.equations_exact ..).mpr parts.1,
           (GeneralNominalCaptureMerges.equations_exact ..).mpr parts.2⟩
        exact both atom (by simpa only [observed] using member)

/-- Source validity and the entire cross matrix leave precisely the extrema
obligation for propagation in this particular model. -/
theorem propagate_iff_extrema (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (propagate state registry invocation declaration bindings) model ↔
    GeneralNominalState.Models state model ∧ Compatible bindings model ∧
      CaptureExtrema state registry invocation declaration bindings model := by
  rw [propagate_models,merges_iff_extrema]

end Yulang.GeneralNominalMergeResidual178
