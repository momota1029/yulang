import Yulang.GeneralRebaseInstallPublicObstruction279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9300000
namespace Yulang.GeneralRebaseFiniteProbeObstruction279
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseInstallNovelty279 (LostModel)

theorem eventual_agreement {α : Type} (enter installed : Nat → α → Prop)
    (decrease : ∀ {i j}, i ≤ j → ∀ x, enter j x → enter i x)
    (restriction : ∀ n x, installed n x → enter n x)
    (next : ∀ n x, enter (n+1) x → installed n x) (probes : List α) :
    ∃ cutoff, ∀ n, cutoff ≤ n → ∀ x ∈ probes, installed n x ↔ enter n x := by
  classical
  induction probes with
  | nil =>
    exact ⟨0,fun _ _ _ none => False.elim (List.not_mem_nil none)⟩
  | cons front rest ih =>
    obtain ⟨old,hold⟩ := ih
    by_cases fails : ∃ i, ¬ enter i front
    · obtain ⟨i,lost⟩ := fails
      refine ⟨max old i,?_⟩
      intro n upper x member
      rcases List.mem_cons.mp member with rfl | tail
      · refine ⟨restriction n x,fun h => False.elim (lost (decrease (Nat.le_trans (Nat.le_max_right ..) upper) x h))⟩
      · exact hold n (Nat.le_trans (Nat.le_max_left ..) upper) x tail
    · have all : ∀ j, enter j front := fun j => Classical.byContradiction (fun h => fails ⟨j,h⟩)
      refine ⟨old,?_⟩
      intro n upper x member
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨restriction n x,fun _ => next n x (all _)⟩
      · exact hold n upper x tail

namespace V
open GeneralDictionaryVersionLoopSource237 (registry root)
open GeneralDictionaryVersionLoopIteration239 (state)
open GeneralRebaseVersionMicro278 (installed refreshed install_step refresh_step reobserve_step)
open GeneralRebaseInstallTimeline278.Version (round_restriction)
open GeneralRebaseInstallPublicObstruction279.Version (e full_assignment_lost edges_equal)
open GeneralNominalVersionedMixedKernel234 (step_models)

theorem finite_tests (probes : List Assignment) :
    ∃ cutoff, ∀ n, cutoff ≤ n →
      (∀ m ∈ probes, Models (installed n) m ↔ Models (state n) m) ∧
      LostModel (state n) (e n) ∧
      (installed n).core.erased.current.edges = (state n).core.erased.current.edges := by
  obtain ⟨n,agrees⟩ := eventual_agreement (fun i m => Models (state i) m)
    (fun i m => Models (installed i) m)
    (fun {i j} ordered => round_restriction i j ordered)
    (fun i _ good => step_models (install_step i) good)
    (fun i _ good => step_models (refresh_step i) (step_models (reobserve_step i) good)) probes
  exact ⟨n,fun k beyond => ⟨agrees k beyond,full_assignment_lost k,edges_equal k⟩⟩
end V

namespace L
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralRebaseLooseMicro278 (installed refreshed install_step refresh_step reobserve_step point_models)
open GeneralRebaseInstallTimeline278.Loose (round_restriction)
open GeneralRebaseInstallPublicObstruction279.Loose (e full_assignment_lost edges_equal)

theorem finite_tests (probes : List Assignment) :
    ∃ cutoff, ∀ n, cutoff ≤ n →
      (∀ m ∈ probes, Models (installed n) m ↔ Models (state n) m) ∧
      LostModel (state n) (e n) ∧
      (installed n).core.erased.current.edges = (state n).core.erased.current.edges := by
  obtain ⟨n,agrees⟩ := eventual_agreement (fun i m => Models (state i) m)
    (fun i m => Models (installed i) m)
    (fun {i j} ordered => round_restriction i j ordered)
    (fun i _ good => point_models (install_step i) good)
    (fun i _ good => point_models (refresh_step i) (point_models (reobserve_step i) good)) probes
  exact ⟨n,fun k beyond => ⟨agrees k beyond,full_assignment_lost k,edges_equal k⟩⟩
end L

end Yulang.GeneralRebaseFiniteProbeObstruction279
