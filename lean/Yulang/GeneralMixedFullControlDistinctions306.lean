import Yulang.GeneralMixedFullControlPresentation306
import Yulang.GeneralMixedFullControlCost306
import Yulang.GeneralMixedFullControlObserver306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlDistinctions306
open GeneralDictionaryOutputDepth252 (roles initial registry root sourceRegistry)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralMixedFullControlCode306 (Code code marker)
open GeneralMixedFullControlTrace306 (all_constructible)
open GeneralMixedFullControlMinimalRaw306 (Reach)
open GeneralMixedFullControlCompiledQuotient306 (colored uncolored)
open GeneralMixedFullControlPresentation306 (uncolored_exact colored_exact)
open GeneralMixedFullControlMinimal306 (obligations)
open GeneralMixedFullControlCost306 (finishing_lengths)
open GeneralMixedFullControlObserver306 (selected_all)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthSchedule286 (Halted)

theorem blind_quotient_loses_model_observation :
    ∃ s t : State roles, Reach s ∧ Reach t ∧
      uncolored.project (code s) = uncolored.project (code t) ∧
      colored.project (code s) ≠ colored.project (code t) ∧
      Local sourceRegistry s root (.selected 0 []) ∧ Local sourceRegistry t root (.selected 0 []) ∧
      Models s smallModel ∧ ¬ Models t smallModel := by
  let before : Code := ⟨false,⟨true,true⟩⟩
  let after : Code := ⟨true,⟨true,false⟩⟩
  obtain ⟨s,ns,ps,x⟩ := all_constructible before
  obtain ⟨t,nt,pt,y⟩ := all_constructible after
  have been := (marker ps).2.mp (congrArg Code.installed x)
  have now := (marker pt).1.mp (congrArg Code.installed y)
  refine ⟨s,t,⟨ns,ps⟩,⟨nt,pt⟩,(uncolored_exact ⟨ns,ps⟩ ⟨nt,pt⟩).mpr ?_,?_,
    selected_all ps,selected_all pt,
    (been.anchor.models _).mpr ((GeneralRebaseDepthPreAnchor286.initial_models _).mp small_initial),?_⟩
  · rw [x,y]
    rfl
  · intro merged
    have eq := (colored_exact ⟨ns,ps⟩ ⟨nt,pt⟩).mp merged
    rw [x,y] at eq
    have impossible : false = true := congrArg Prod.fst eq
    cases impossible
  · intro m
    exact GeneralRebaseDepthMinimal285.scalar_ne_output ((GeneralRebaseDepthPostQueries286.models now _).mp m).2

theorem same_obligation_count_different_best_raw_length :
    ∃ s t : State roles, Reach s ∧ Reach t ∧
      obligations (code s) = obligations (code t) ∧
      (∃ t, ActualPath s t 1 ∧ Halted t) ∧ ¬ (∃ u, ActualPath t u 1 ∧ Halted u) := by
  let batch : Code := ⟨true,⟨false,false⟩⟩
  let separate : Code := ⟨false,⟨true,false⟩⟩
  obtain ⟨s,ns,ps,x⟩ := all_constructible batch
  obtain ⟨t,nt,pt,y⟩ := all_constructible separate
  refine ⟨s,t,⟨ns,ps⟩,⟨nt,pt⟩,?_,(finishing_lengths ps 1).mpr ?_,?_⟩
  · rw [x,y]
    rfl
  · rw [x]
    decide +kernel
  · intro realized
    have possible := (finishing_lengths pt 1).mp realized
    rw [y] at possible
    have impossible : ¬ (GeneralMixedFullControlScheduler306.leastCost separate ≤ 1) := by decide +kernel
    exact impossible possible.1

end Yulang.GeneralMixedFullControlDistinctions306
