import Yulang.GeneralGeneratedDictionaryRankBook299
import Yulang.GeneralGeneratedDictionarySlice299
import Yulang.GeneralGeneratedDisplayPhase299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedDictionaryRootedFixtures299
open GeneralNominalExamples (registry displayRoot model)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299 (Edge)
open GeneralGeneratedMixedRooted299 (Rooted after_halt)
open GeneralGeneratedDictionarySlice299 (restrict keys)
open GeneralGeneratedDictionaryRankBook299 (ranks get ready)
open GeneralGeneratedDisplayObserved299 (observedTable checked_rows)
open GeneralGeneratedDisplayTable299 (table decode)
open B4TargetV8

theorem rooted_observed : Rooted observedTable 0 := by
  intro i row hit
  rw [checked_rows] at hit ⊢
  rcases GeneralGeneratedDisplayTable299.rows i row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact .inl rfl
  · exact .inr (.single ⟨⟨1,[1]⟩,rfl,List.mem_singleton_self _⟩)

theorem actual_from_rooted :
    Classify (boundary roles) registry after displayRoot (.selected (.node 1 [.node 3 []])) ∧
    (∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []])) := by
  have supplied : GeneralGeneratedMixedCurrentNodes299.Providers registry after observedTable decode := by
    rw [checked_rows]
    exact GeneralGeneratedDisplayBothCurrent299.providers
  have seen : run observedTable 2 0 = some (.node 1 [.node 3 []]) := by
    rw [checked_rows]
    exact GeneralGeneratedDisplayTable299.computed_root
  exact after_halt observedTable decode 0 rfl rooted_observed
    GeneralRebaseCompiledInstall277.reachable GeneralGeneratedDisplayObserved299.faithful supplied
    GeneralRebasePackedNodeCompose298.no_second_raw_step 2 _ seen

theorem actual_rank_book :
    get 0 (ranks observedTable [0,1] 2) = some 2 ∧
    get 1 (ranks observedTable [0,1] 2) = some 1 ∧ ready observedTable [0,1] 2 = true :=
  ⟨rfl,rfl,rfl⟩

def unrelated : Read
  | 0 => some ⟨2,[1]⟩
  | 1 => some ⟨4,[]⟩
  | 8 => some ⟨8,[8]⟩
  | _ => none

def rootSlice : Read := restrict unrelated (keys unrelated 2 0)

theorem actual_keys : keys unrelated 2 0 = [0,1] := rfl

theorem clean_slice : (run rootSlice 2 0 = some (.node 2 [.node 4 []])) ∧
    Rooted rootSlice 0 ∧ Closed rootSlice := by
  exact ⟨GeneralGeneratedDictionarySlice299.at_root unrelated 2 0 _ rfl,
    GeneralGeneratedDictionarySlice299.rooted unrelated 2 0,
    GeneralGeneratedDictionarySlice299.closed_slice unrelated 2 0 _ rfl⟩

theorem disjoint_cycle_control :
    ready unrelated [0,1,8] 3 = false ∧ ready rootSlice [0,1] 2 = true := ⟨rfl,rfl⟩

end Yulang.GeneralGeneratedDictionaryRootedFixtures299
