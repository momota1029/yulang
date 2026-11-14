import Yulang.GeneralRegistryChildOrder

/-! A fixed representative of the full visible/where reordering class. -/
namespace Yulang.GeneralCanonicalRegistry
open GeneralDeclarations GeneralRegistryReordering GeneralRegistryChildOrder

noncomputable def canonical (registry : Registry) : Registry :=
  Classical.choose (show ∃ other, Reorders registry other from ⟨registry,reorders_refl registry⟩)

theorem reorders_canonical (registry : Registry) : Reorders registry (canonical registry) :=
  Classical.choose_spec (show ∃ other, Reorders registry other from ⟨registry,reorders_refl registry⟩)

theorem class_iff (order : Reorders first last) (other : Registry) :
    Reorders first other ↔ Reorders last other :=
  ⟨reorders_trans (reorders_symm order),reorders_trans order⟩

theorem canonical_eq (order : Reorders first last) : canonical first = canonical last := by
  have congruent {p q : Registry → Prop} (one : ∃ r, p r) (two : ∃ r, q r)
      (same : ∀ r, p r ↔ q r) : Classical.choose one = Classical.choose two := by
    have equal : p = q := funext (fun r => propext (same r))
    cases equal
    rfl
  exact congruent _ _ (class_iff order)

theorem canonical_idempotent (registry : Registry) : canonical (canonical registry) = canonical registry :=
  (canonical_eq (reorders_canonical registry)).symm

theorem canonical_checked (checked : Checked registry) : Checked (canonical registry) :=
  reorders_checked (reorders_canonical registry) checked

theorem constructors (registry : Registry) : (canonical registry).constructors = registry.constructors :=
  (reorders_canonical registry).1.symm

theorem roles (registry : Registry) : (canonical registry).roles = registry.roles :=
  (reorders_canonical registry).2.1.symm

theorem canonical_eq_iff : canonical first = canonical last ↔ Reorders first last := by
  constructor
  · intro same
    exact reorders_trans (reorders_canonical first)
      (same ▸ reorders_symm (reorders_canonical last))
  · exact canonical_eq

end Yulang.GeneralCanonicalRegistry
