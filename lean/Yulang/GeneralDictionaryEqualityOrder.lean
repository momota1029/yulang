import Yulang.GeneralDictionaryEqualityStepBound

/-! Semantic order-independence of the completed finite equality subphase.
Only registered-source raw equality is compared, not states, descriptor
canonicality, the full inference execution, or V5 canonicalLocalOrder. -/
namespace Yulang.GeneralDictionaryEqualityOrder
open GeneralNominalSaturationState GeneralNominalFeedbackSteps
open GeneralDictionaryEqualityObservations GeneralDictionaryFiniteEqualityCompletion
variable {roles : Roles.RoleDecls}

/-- Every journal-entailed equality certificate preserves the entire semantic
equality theory, not only the finitely listed pairs it materializes. -/
theorem semantic_equal_iff {before after : State roles} (path : Equates before after)
    (first last : Nat) :
    GeneralNominalFeedbackK2.Equal after first last ↔ GeneralNominalFeedbackK2.Equal before first last := by
  constructor
  · intro equal model valid
    exact equal model ((path.models model).mpr valid)
  · intro equal model valid
    exact equal model ((path.models model).mp valid)

/-- At a completed endpoint, raw equality on old registered sources is EXACTLY
the original journal's semantic equality. No full ContextComplete is required. -/
theorem completed_raw_iff {before after : State roles} (path : Equates before after)
    (complete : EqualityComplete after) (first last : Nat)
    (one : first ∈ GeneralNominalState.sources before.context.state)
    (two : last ∈ GeneralNominalState.sources before.context.state) :
    RawEqual after first last ↔ GeneralNominalFeedbackK2.Equal before first last := by
  constructor
  · intro raw
    apply (semantic_equal_iff path first last).mp
    exact fun model valid => raw model valid.1
  · intro equal
    exact complete first ((GeneralDictionaryEqualityStepBound.Equates.sources path first).mpr one)
      last ((GeneralDictionaryEqualityStepBound.Equates.sources path last).mpr two)
      ((semantic_equal_iff path first last).mpr equal)

/-- Any two completed equality-only paths have the same registered-source
raw equality observations, even if they add constraints in different orders
or retain different redundant equation lists. This is not state equality. -/
theorem completed_orders {before left right : State roles}
    (firstPath : Equates before left) (lastPath : Equates before right)
    (firstComplete : EqualityComplete left) (lastComplete : EqualityComplete right)
    (a b : Nat) (one : a ∈ GeneralNominalState.sources before.context.state)
    (two : b ∈ GeneralNominalState.sources before.context.state) :
    RawEqual left a b ↔ RawEqual right a b :=
  (completed_raw_iff firstPath firstComplete a b one two).trans
    (completed_raw_iff lastPath lastComplete a b one two).symm

end Yulang.GeneralDictionaryEqualityOrder
