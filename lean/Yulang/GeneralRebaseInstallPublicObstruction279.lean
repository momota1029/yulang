import Yulang.GeneralRebaseInstallTimeline278
import Yulang.GeneralRebaseWitnessRegressions279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseInstallPublicObstruction279
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseInstallNovelty279 (LostModel)
open GeneralNominalVersionedChildren232 (edges)
open GeneralRebaseRoundMicro278 (Tick)

namespace Version
open GeneralDictionaryVersionLoopSource237 (registry root)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralRebaseVersionMicro278 (installed exact_public install_step)
open GeneralVersionBoundaryCompletion259 (Agree)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)

noncomputable abbrev e (n : Nat) := GeneralDictionaryVersionLoopInstall239.chosen (stages n).shape

theorem edges_equal (n : Nat) :
    (installed n).core.erased.current.edges = (state n).core.erased.current.edges := by
  change (state n).core.erased.current.edges ++ edges (plan n) = _
  unfold edges
  rw [GeneralDictionaryVersionLoopFrame239.children_empty]
  simp only [List.map_nil,List.append_nil]

theorem public_iff (n : Nat) (p : Assignment) :
    (∃ m, Agree m p ∧ Models (installed n) m) ↔ (∃ m, Agree m p ∧ Models (state n) m) :=
  (exact_public ⟨n,.installed⟩ p).trans (exact_public ⟨n,.enter⟩ p).symm

theorem full_assignment_lost (n : Nat) : LostModel (state n) (e n) := by
  refine ⟨bad n,(GeneralRebaseInstallTimeline278.Version.enter_patch n n).mpr (Nat.le_refl _),?_⟩
  intro valid
  have cannot : n+1 ≤ n := (GeneralRebaseInstallTimeline278.Version.patch_exact ⟨n,.installed⟩ n).mp valid
  omega

theorem actual_loss_and_same_public (n : Nat) :
    GeneralNominalVersionedMixedKernel234.Step registry root (state n) (installed n) ∧
    LostModel (state n) (e n) ∧
    (installed n).core.erased.current.edges = (state n).core.erased.current.edges ∧
    ∀ p, (∃ m, Agree m p ∧ Models (installed n) m) ↔ (∃ m, Agree m p ∧ Models (state n) m) :=
  ⟨install_step n,full_assignment_lost n,edges_equal n,public_iff n⟩

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (registry root)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralRebaseLooseMicro278 (installed exact_public install_step)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralDictionaryLooseFamilyNovel240 (bad)

noncomputable abbrev e (n : Nat) := GeneralDictionaryLooseIterationInstall240.chosen (stages n).shape

theorem edges_equal (n : Nat) :
    (installed n).core.erased.current.edges = (state n).core.erased.current.edges := by
  change (state n).core.erased.current.edges ++ edges (plan n) = _
  unfold edges
  rw [GeneralDictionaryLooseIterationFrame240.children_empty]
  simp only [List.map_nil,List.append_nil]

theorem public_iff (n : Nat) (p : Assignment) :
    (∃ m, Agree m p ∧ Models (installed n) m) ↔ (∃ m, Agree m p ∧ Models (state n) m) :=
  (exact_public ⟨n,.installed⟩ p).trans (exact_public ⟨n,.enter⟩ p).symm

theorem full_assignment_lost (n : Nat) : LostModel (state n) (e n) := by
  refine ⟨bad n,(GeneralRebaseInstallTimeline278.Loose.enter_patch n n).mpr (Nat.le_refl _),?_⟩
  intro valid
  have cannot : n+1 ≤ n := (GeneralRebaseInstallTimeline278.Loose.patch_exact ⟨n,.installed⟩ n).mp valid
  omega

theorem actual_loss_and_same_public (n : Nat) :
    GeneralNominalPointKernel240.Step registry root (state n) (installed n) ∧
    LostModel (state n) (e n) ∧
    (installed n).core.erased.current.edges = (state n).core.erased.current.edges ∧
    ∀ p, (∃ m, Agree m p ∧ Models (installed n) m) ↔ (∃ m, Agree m p ∧ Models (state n) m) :=
  ⟨install_step n,full_assignment_lost n,edges_equal n,public_iff n⟩

end Loose
end Yulang.GeneralRebaseInstallPublicObstruction279
