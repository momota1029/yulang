import Yulang.GeneralNominalLocalBoundary

/-! Local classification depends only on its five diagnostic predicates. -/
namespace Yulang.GeneralLocalPredicateCongruence
open GeneralNominalLocalBoundary CommonRoleOutermostResolver
universe u
variable {v : B4Target.Vocabulary.{u}} {first last : Fields v}
variable {r₁ r₂ : v.Registry} {s₁ s₂ : v.State} {d : v.Demand}

theorem local_iff (pending : first.RootPending r₁ s₁ d ↔ last.RootPending r₂ s₂ d)
    (root : first.RootK2 r₁ s₁ d ↔ last.RootK2 r₂ s₂ d)
    (candidate : first.CandidateK2 r₁ s₁ d ↔ last.CandidateK2 r₂ s₂ d)
    (inspection : first.InspectionPending r₁ s₁ d ↔ last.InspectionPending r₂ s₂ d)
    (survivor : ∀ key children, first.Survivor r₁ s₁ d key children ↔ last.Survivor r₂ s₂ d key children)
    (frontier : Frontier v.Demand) :
    Local first r₁ s₁ d frontier ↔ Local last r₂ s₂ d frontier := by
  have safe : SafeKnown first r₁ s₁ d ↔ SafeKnown last r₂ s₂ d :=
    and_congr (not_congr pending) (and_congr (not_congr root)
      (and_congr (not_congr candidate) (not_congr inspection)))
  have rejection : RejectReason first r₁ s₁ d ↔ RejectReason last r₂ s₂ d := by
    unfold RejectReason
    simp only [pending,root,candidate,inspection,survivor]
  constructor
  · intro given
    cases given with
    | pending h => exact .pending (pending.mp h)
    | inspectionPending h p r c =>
        exact .inspectionPending ((not_congr pending).mp h)
          (inspection.mp p) ((not_congr root).mp r) ((not_congr candidate).mp c)
    | rejected h => exact .rejected (rejection.mp h)
    | ambiguous h a b different =>
        exact .ambiguous (safe.mp h)
          ((survivor _ _).mp a) ((survivor _ _).mp b) different
    | selected h unique =>
        exact .selected (safe.mp h)
          ⟨(survivor _ _).mp unique.1,fun key children found => unique.2 key children ((survivor _ _).mpr found)⟩
  · intro given
    cases given with
    | pending h => exact .pending (pending.mpr h)
    | inspectionPending h p r c =>
        exact .inspectionPending ((not_congr pending).mpr h)
          (inspection.mpr p) ((not_congr root).mpr r) ((not_congr candidate).mpr c)
    | rejected h => exact .rejected (rejection.mpr h)
    | ambiguous h a b different =>
        exact .ambiguous (safe.mpr h)
          ((survivor _ _).mpr a) ((survivor _ _).mpr b) different
    | selected h unique =>
        exact .selected (safe.mpr h)
          ⟨(survivor _ _).mpr unique.1,fun key children found => unique.2 key children ((survivor _ _).mp found)⟩

end Yulang.GeneralLocalPredicateCongruence
