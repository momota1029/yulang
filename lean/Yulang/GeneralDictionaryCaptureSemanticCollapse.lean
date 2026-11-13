import Yulang.GeneralDictionarySemanticSchemaTransport

/-! Duplicate observations may occupy different source identities. Semantic
endpoint equivalence suffices for the old merged capture to agree with the
new singleton. Current merge constraints are not assumed in this direction. -/
namespace Yulang.GeneralDictionaryCaptureSemanticCollapse
open GeneralNominalAllocation GeneralNominalCaptureMerges GeneralDeclarations
open CommonNominalFullCarrier

theorem capture_fits (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (first second : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (declared : name ∈ declaration.inputNames)
    (old : GeneralNominalState.Models
      (propagate state registry invocation declaration [(name,first),(name,second)]) model)
    (lo : Equivalent (model first.1).1 (model second.1).1)
    (hi : Equivalent (model first.2).1 (model second.2).1) (actual : Ty) :
    Fits model ((capture state registry invocation declaration.id [(name,first),(name,second)]).inputs name) actual ↔
      Fits model first actual := by
  rw [capture_interval_exact state registry invocation declaration _ model
    ((propagate_models ..).mp old).2.2 name declared (by simp [occurrences])]
  have occ : occurrences [(name,first),(name,second)] name = [first,second] := by simp [occurrences]
  rw [occ]
  constructor
  · intro h; exact h first (by simp)
  · intro h pair member
    rcases List.mem_cons.mp member with rfl | rest
    · exact h
    · have eq := List.mem_singleton.mp rest
      subst pair
      exact (GeneralDictionarySemanticSchemaTransport.fits_endpoints model first second actual lo hi).mp h

theorem endpoints (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (first second : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (declared : name ∈ declaration.inputNames)
    (old : GeneralNominalState.Models
      (propagate state registry invocation declaration [(name,first),(name,second)]) model)
    (lo : Equivalent (model first.1).1 (model second.1).1)
    (hi : Equivalent (model first.2).1 (model second.2).1) :
    let merged := (capture state registry invocation declaration.id [(name,first),(name,second)]).inputs name
    Equivalent (model merged.1).1 (model first.1).1 ∧ Equivalent (model merged.2).1 (model first.2).1 := by
  dsimp only
  apply GeneralDictionaryCaptureMultiplicity.endpoints_of_fits
  · exact GeneralDictionaryCapturedChildIntervals.capture_order state registry invocation declaration _ model old name declared
  · exact ((propagate_models ..).mp old).2.1 (name,first) (by simp) (name,first) (by simp) rfl
  · exact capture_fits state registry invocation declaration name first second model declared old lo hi

/-- The original private propagation gives the singleton's entire new propagation
once the current base model is known, even when the dropped source IDs differ. -/
theorem propagation (a b : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (first second : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (names : declaration.inputNames = [name])
    (old : GeneralNominalState.Models
      (propagate a registry invocation declaration [(name,first),(name,second)]) model)
    (current : GeneralNominalState.Models b model) :
    GeneralNominalState.Models (propagate b registry invocation declaration [(name,first)]) model := by
  have parts := (propagate_models ..).mp old
  apply (propagate_models ..).mpr
  refine ⟨current,?_,?_⟩
  · intro x hx y hy same
    have ex := List.mem_singleton.mp hx
    have ey := List.mem_singleton.mp hy
    subst x; subst y
    exact parts.2.1 (name,first) (by simp) (name,first) (by simp) rfl
  · simp [merges,names,occurrences,PresenceNormalForm.All]
end Yulang.GeneralDictionaryCaptureSemanticCollapse
