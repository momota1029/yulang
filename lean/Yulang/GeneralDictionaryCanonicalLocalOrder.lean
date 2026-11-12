import Yulang.GeneralNominalLocalReordering

/-! The exact executor-dependent V5 order obligation, factored into proved
registry invariance and still-needed final-state classification agreement.
Literal state equality is sufficient but is not required by the factorization. -/
namespace Yulang.GeneralDictionaryCanonicalLocalOrder

open GeneralDictionaryReachableBoundary
open B4TargetV5
open B4TargetV3 (Executor Local)

/-- Literally the canonicalLocalOrder field of the existing Remaining record. -/
def CanonicalLocalOrder (roles : Roles.RoleDecls)
    (e : Executor (GeneralNominalFeedbackBoundary.vocabulary roles)) : Prop :=
  ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
    (boundary roles).Reorders r r' → ∀ s root, Reachable (boundary roles) r root s →
    Reachable (boundary roles) r' root s → ∀ d f,
    Local (boundary roles).toSourceBoundary r (e.run r s root).1 d f ↔
      Local (boundary roles).toSourceBoundary r' (e.run r' s root).1 d f

theorem remaining_field (roles : Roles.RoleDecls)
    (e : Executor (GeneralNominalFeedbackBoundary.vocabulary roles))
    (remaining : GeneralDictionaryReachableObligations.Remaining roles e) :
    CanonicalLocalOrder roles e := remaining.canonicalLocalOrder

/-- Both returned states are compared under one fixed registry. This retains
all final-state quantifiers while removing the already-proved registry change. -/
def FinalStateAgreement (roles : Roles.RoleDecls)
    (e : Executor (GeneralNominalFeedbackBoundary.vocabulary roles)) : Prop :=
  ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
    (boundary roles).Reorders r r' → ∀ s root, Reachable (boundary roles) r root s →
    Reachable (boundary roles) r' root s → ∀ d f,
    Local (boundary roles).toSourceBoundary r' (e.run r s root).1 d f ↔
      Local (boundary roles).toSourceBoundary r' (e.run r' s root).1 d f

theorem exact_factorization (roles : Roles.RoleDecls)
    (e : Executor (GeneralNominalFeedbackBoundary.vocabulary roles)) :
    CanonicalLocalOrder roles e ↔ FinalStateAgreement roles e := by
  constructor
  · intro order r r' checked checked' reordered s root reachable reachable' d f
    exact (GeneralNominalLocalReordering.boundary_local reordered checked.1 _ d f).symm.trans
      (order r r' checked checked' reordered s root reachable reachable' d f)
  · intro agree r r' checked checked' reordered s root reachable reachable' d f
    exact (GeneralNominalLocalReordering.boundary_local reordered checked.1 _ d f).trans
      (agree r r' checked checked' reordered s root reachable reachable' d f)

theorem of_returned_state_equality (roles : Roles.RoleDecls)
    (e : Executor (GeneralNominalFeedbackBoundary.vocabulary roles))
    (same : ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
      (boundary roles).Reorders r r' → ∀ s root, Reachable (boundary roles) r root s →
      Reachable (boundary roles) r' root s → (e.run r s root).1 = (e.run r' s root).1) :
    CanonicalLocalOrder roles e :=
  GeneralNominalLocalReordering.canonicalLocalOrder_of_returned_state_equality roles e same

end Yulang.GeneralDictionaryCanonicalLocalOrder
