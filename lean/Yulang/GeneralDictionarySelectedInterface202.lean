import Yulang.B4SkeletonV7

namespace Yulang.GeneralDictionarySelectedInterface202
open CommonRoleOutermostResolver
universe u
variable {v : B4Target.Vocabulary.{u}}

/-- The I34 replacement, with the original V5 quantifier and premise order. -/
def SelectedEvidenceNode (b : B4TargetV6.SourceBoundary v) : Prop :=
  ∀ r, b.Checked r → ∀ s root, B4TargetV6.Reachable b r root s → ∀ model,
    b.Models s model → ∀ d key children dictionaries,
    (d = root ∨ b.Generated r s root d) → b.Stable r s d →
    (∀ child, child ∈ children → b.Stable r s child) →
    B4TargetV6.SafeKnown b r s d → B4TargetV6.Unique b r s d key children →
    ¬ b.OutputConflict r s d key →
    All₂ (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
    b.Evidence r s model d (.node key dictionaries)

def SelectedEvidenceAt (b : B4TargetV6.SourceBoundary v) (r : v.Registry)
    (s : v.State) (root : v.Demand) : Prop :=
  ∀ model, b.Models s model → ∀ d key children dictionaries,
    (d = root ∨ b.Generated r s root d) → b.Stable r s d →
    (∀ child, child ∈ children → b.Stable r s child) →
    B4TargetV6.Local b r s d (.selected key children) →
    All₂ (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
    b.Evidence r s model d (.node key dictionaries)

theorem selected_iff (b : B4TargetV6.SourceBoundary v) : SelectedEvidenceNode b ↔
    ∀ r, b.Checked r → ∀ s root, B4TargetV6.Reachable b r root s → SelectedEvidenceAt b r s root := by
  constructor
  · intro node r checked s root reachable model valid d key children dictionaries reached stable childStable selected evidence
    cases selected with
    | selected safe unique clear =>
        exact node r checked s root reachable model valid d key children dictionaries reached stable childStable safe unique clear evidence
  · intro node r checked s root reachable model valid d key children dictionaries reached stable childStable safe unique clear evidence
    exact node r checked s root reachable model valid d key children dictionaries reached stable childStable
      (.selected safe unique clear) evidence

theorem to_v7 (b : B4TargetV7.SourceBoundary v)
    (node : SelectedEvidenceNode b.toV6) : B4SkeletonV7.EvidenceNode b := by
  intro r checked s root reachable model valid d key children dictionaries reached stable childStable selected evidence
  exact (selected_iff b.toV6).mp node r checked s root reachable model valid d key children dictionaries
    reached stable childStable (B4TargetV7.selected_iff.mp selected).1 evidence

theorem evidenceAt_of_empty_models (b : B4TargetV6.SourceBoundary v) (r : v.Registry)
    (s : v.State) (root : v.Demand) (empty : ¬ ∃ model, b.Models s model) :
    SelectedEvidenceAt b r s root := by
  intro model valid
  exact False.elim (empty ⟨model,valid⟩)

end Yulang.GeneralDictionarySelectedInterface202
