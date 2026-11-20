import Yulang.GeneralDepthTwoObserved300
import Yulang.GeneralDepthTwoFinalCurrent300
import Yulang.GeneralGeneratedMixedRooted299
import Yulang.GeneralGeneratedDictionaryRankBook299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDepthTwoCertifiedRead300
open GeneralGeneratedNestedSource299 (initial root)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final actual_terminal)
open GeneralDepthTwoFinalNodes300
open GeneralDepthTwoFinalScope300 (generated_only)
open GeneralDepthTwoFinalHalt300 (source_halted)
open GeneralDepthTwoFinalCurrent300 (current)
open GeneralDepthTwoObserved300 (table decode entries faithful computed)
open GeneralGeneratedMixedCurrentNodes299 (Providers)
open GeneralGeneratedMixedRooted299 (Rooted after_halt)
open GeneralGeneratedDictionaryAcc299 (Edge)
open GeneralGeneratedDictionaryRun299 (run)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open CommonRoleOutermostResolver (Frontier Dictionary Child)
open B4TargetV8

theorem providers : Providers registry final table decode := by
  intro i row hit _
  rcases entries i row hit with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
  · exact ⟨_,current .outer⟩
  · exact ⟨_,current .inner⟩
  · exact ⟨_,current .leaf⟩

theorem rooted : Rooted table 0 := by
  intro i row hit
  rcases entries i row hit with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
  · exact .inl rfl
  · exact .inr (.single ⟨⟨1,[1]⟩,rfl,List.mem_singleton_self _⟩)
  · exact .inr (.tail (.single ⟨⟨1,[2]⟩,rfl,List.mem_singleton_self _⟩)
      ⟨⟨1,[1]⟩,rfl,List.mem_singleton_self _⟩)

theorem compiled_final :
    Classify (boundary roles) registry final root (.selected (.node 1 [.node 1 [.node 3 []]])) ∧
    ∀ m, Models final m → (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]]) :=
  after_halt table decode 0 rfl rooted actual_terminal.2.1 faithful providers source_halted 3 _ computed

theorem chosen_generated (n : Node) :
    demand n = root ∨ (boundary roles).Generated registry final root (demand n) := by
  cases n
  · exact .inl rfl
  · exact .inr (.child .root (GeneralDepthTwoEvidence300.final_edges ▸ List.mem_cons_self ..))
  · exact .inr actual_terminal.2.2

theorem curr_enabled (n : Node) :
    GeneralNominalVersionedMixedKernel234.Installable compiled final (GeneralDepthTwoFinalCurrent300.certificate n) :=
  GeneralNominalVersionedMixedCurrentCandidate235.source_installable (current n)
    actual_terminal.2.1 (GeneralDepthTwoFinalSelection300.selected n)

theorem all_chosen_committed (n : Node) :
    GeneralNominalVersionedMixedKernel234.Committed final (plan n) := by
  apply GeneralDepthTwoFinalScope300.no_raw_install (GeneralDepthTwoFinalCurrent300.certificate n) (curr_enabled n)
  change (boundary roles).Generated registry final root (plan n).packet.site.occurrence
  rw [GeneralDepthTwoFinalScope300.site_focus]
  rcases chosen_generated n with eq|direct
  · rw [eq]; exact .root
  · exact direct

theorem evidence_at : B4SkeletonV8.EvidenceAt (boundary roles) registry final root := by
  intro m valid focus k children ds reached stable _ selected childEvidence
  have covered : ∃ n, focus = demand n := by
    rcases reached with rfl|generated
    · exact ⟨.outer,rfl⟩
    · exact generated_only focus generated
  obtain ⟨n,rfl⟩ := covered
  exact GeneralNominalVersionedMixedStableEvidence235.selected_node stable
    (curr_enabled n) (current n).occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) valid childEvidence

theorem checked_rank :
    GeneralGeneratedDictionaryRankBook299.get 0 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 3 ∧
    GeneralGeneratedDictionaryRankBook299.get 1 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 2 ∧
    GeneralGeneratedDictionaryRankBook299.get 2 (GeneralGeneratedDictionaryRankBook299.ranks table [0,1,2] 3) = some 1 :=
  ⟨rfl,rfl,rfl⟩

end Yulang.GeneralDepthTwoCertifiedRead300
