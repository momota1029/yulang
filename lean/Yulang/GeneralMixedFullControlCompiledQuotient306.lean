import Yulang.GeneralFiniteColoredQuotient306
import Yulang.GeneralMixedFullControlModelClasses306

set_option maxHeartbeats 8000000
namespace Yulang.GeneralMixedFullControlCompiledQuotient306
open GeneralFiniteColoredQuotient306 (fastQuotient fast_exact exact_edges projection_total projection_respects)
open GeneralFiniteColoredEquivalence306 (test_exact)
open GeneralFiniteColoredRounds306 (Closed)
open GeneralMixedFullControlCode306 (Code code)
open GeneralMixedFullControlUnlabelled306 (targets codes all_codes raw_exact)
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)

theorem code_closed : Closed targets codes :=
  fun _ _ _ h => (List.mem_filter.mp h).1

def uncolored := fastQuotient targets (fun _ => ()) codes
def colored := fastQuotient targets Code.installed codes

theorem executed_counts :
    uncolored.representatives.length = 5 ∧ colored.representatives.length = 6 := by decide +kernel

theorem raw_edges {β : Type} [DecidableEq β] (obs : Code → β)
    {s : State roles} {n : Nat} (path : ActualPath initial s n)
    (r q : Code) (chosen : (fastQuotient targets obs codes).project (code s) = some r) :
    q ∈ (fastQuotient targets obs codes).edges r ↔
      ∃ t, Step registry root s t ∧ (fastQuotient targets obs codes).project (code t) = some q := by
  rw [fast_exact] at chosen ⊢
  rw [exact_edges code_closed (all_codes _) chosen]
  constructor
  · rintro ⟨y,edge,tag⟩
    obtain ⟨t,act,atCode⟩ := (raw_exact path y).mp (List.mem_filter.mp edge).2
    exact ⟨t,act,atCode.symm ▸ tag⟩
  · rintro ⟨t,act,tag⟩
    exact ⟨code t,List.mem_filter.mpr ⟨all_codes _,(raw_exact path _).mpr ⟨t,act,rfl⟩⟩,tag⟩

theorem colored_preserves_full_models {s t : State roles} {ns nt : Nat}
    (ps : ActualPath initial s ns) (pt : ActualPath initial t nt)
    (same : colored.project (code s) = colored.project (code t)) :
    ∀ m, Models s m ↔ Models t m := by
  unfold colored at same
  rw [fast_exact] at same
  have pair := (projection_respects code_closed (all_codes (code s)) (all_codes (code t))).mp same
  obtain ⟨_,bisim,holds⟩ := (test_exact code_closed (all_codes _) (all_codes _)).mp pair
  exact (GeneralMixedFullControlModelClasses306.phase_iff_models ps pt).mp
    (bisim _ (all_codes _) _ (all_codes _) holds).1

theorem clean_closed_projection (x : Code) : ∃ y, colored.project x = some y := by
  unfold colored
  rw [fast_exact]
  exact projection_total code_closed (all_codes _)

end Yulang.GeneralMixedFullControlCompiledQuotient306
