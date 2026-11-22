import Yulang.GeneralDeclarativeCurrentOrigins343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16300
set_option maxHeartbeats 7800000
namespace Yulang.GeneralDeclarativeCurrentRoot343
open GeneralDeclarativeCurrentOrigins343 (done support rootSlice nominal_origin)
open GeneralDeclarativeFrameShape343 (childRows)
open GeneralDeclarativePlacement343 (view rows)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child output targets fallback)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand observedRoot original_arguments)
open GeneralDeclarativeVersionedRootShape342 (spans uses point)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeTaggedElection340 (Ranked Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeGrowth327 (Extends trans facts)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

theorem traced {s : State} (advance : Extends view s) (mode : Mode) :
    Trace (restriction (support advance)) mode 0 (.nominal 0 [.variable 0,.variable 1]) uses :=
  Trace.nominal (args := [2,2]) (alias_refl _) (nominal_origin advance)
    (.cons .capture (.cons .capture .nil))

theorem choice {s : State} (advance : Extends view s) (check : Ranked s rank) :
    Election (support advance) sourceRegistry interpretation waiting actualDemand declaration := by
  refine ⟨?_,⟨rank,check⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · intro a used
    rw [original_arguments] at used
    cases List.mem_singleton.mp used
    exact .inl ⟨_,knows_row (nominal_origin advance) rfl⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,?_⟩
    change All₂ (GeneralDeclarativeTaggedElection340.Head (support advance) sourceRegistry.constructors interpretation)
      actualDemand.arguments declaration.head
    rw [original_arguments]
    exact .cons (.named ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 1],uses,uses,rfl,
      traced advance .lower,traced advance .upper⟩) .nil
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with same|later
    · cases same
      rfl
    · cases List.mem_singleton.mp later
      cases possible.1.2

noncomputable def selected {s : State} (advance : Extends view s) (check : Ranked s rank) :
    Selected (support advance) [] sourceRegistry interpretation waiting actualDemand declaration [child kept] :=
  ⟨rootSlice advance,kept,observedRoot,spans,[],
    GeneralDeclarativeInitialRoot343.exact_inputs done kept,
    fallback,targets,output kept,GeneralDeclarativeOrdinary343.actual kept,
    literal (trans (facts _ rows) advance),fun _ h => h,choice advance check⟩

theorem rule {s : State} (advance : Extends view s) (check : Ranked s rank) :
    Rule (support advance) [] sourceRegistry interpretation waiting actualDemand (.selected declaration.id [child kept]) :=
  .whole (selected advance check)

end Yulang.GeneralDeclarativeCurrentRoot343
