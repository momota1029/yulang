import Yulang.GeneralRebaseFullEdgeProgress279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseClosedEdgeObstruction279
open GeneralDictionaryVersionLoopSource237 (sourceRegistry registry initial root roles)
open GeneralDictionaryVersionLoopInitial238 (initial_source)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseClosedChildShape279 (ClosedArguments)
open GeneralRebaseFullEdgeProgress279 (EdgeFreeModelCover accessible_if_tests_cover)
open GeneralRebaseFullEdgeBasis279 (finite_full_edges OnTrace)
open GeneralNominalCommonBridge (Assignment)

theorem closed : ClosedArguments registry := by
  intro d member c requirement
  have one := List.mem_singleton.mp member
  subst d
  cases requirement

theorem finite_full : ∃ edges : List (GeneralRebaseInstallNovelty279.Edge roles),
    ∀ edge, edge ∈ edges ↔ OnTrace sourceRegistry root initial edge :=
  finite_full_edges initial_source ⟨rfl,GeneralDictionaryVersionLoopSource237.source_checked⟩ closed

theorem no_semantic_test_cover (tests : List Assignment) :
    ¬ EdgeFreeModelCover sourceRegistry root initial tests := by
  intro covers
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc
    (accessible_if_tests_cover initial_source ⟨rfl,GeneralDictionaryVersionLoopSource237.source_checked⟩
      closed tests covers)

end Yulang.GeneralRebaseClosedEdgeObstruction279
