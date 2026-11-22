import Yulang.GeneralDeclarativeRepeatedOrigins348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 37000
set_option maxHeartbeats 55000000
namespace Yulang.GeneralDeclarativeRepeatedRoot348
open GeneralDeclarativeRepeatedOrigins348 (support nominal_origin output_extends rootSlice)
open GeneralDeclarativeRepeatedVisible348 (done)
open GeneralDeclarativeRepeatedPlacement348 (keep placedView requested)
open GeneralDeclarativeReplayCompile348 (output actual)
open GeneralDeclarativeNativeRepeatStage347 (spans fallback)
open GeneralDeclarativeNativeRepeatInput347 (uses exact_inputs)
open GeneralDeclarativeLogicalChild343 (targets)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand observedRoot original_arguments)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralLiveCompoundRegistry316 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeTaggedElection340 (Ranked Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

theorem traced {s : State} (g : Extends placedView s) (mode : Mode) :
    Trace (restriction (support g)) mode 0 (.nominal 0 [.variable 0,.variable 0]) uses :=
  Trace.nominal (args := [2,2]) (alias_refl _) (nominal_origin g)
    (.cons .capture (.cons .capture .nil))

theorem choice {s : State} (g : Extends placedView s) {rank : Nat → Nat} (check : Ranked s rank) :
    Election (support g) sourceRegistry interpretation waiting actualDemand declaration := by
  refine ⟨?_,⟨rank,check⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · intro a used
    rw [original_arguments] at used
    cases List.mem_singleton.mp used
    exact .inl ⟨_,knows_row (nominal_origin g) rfl⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,?_⟩
    change All₂ (GeneralDeclarativeTaggedElection340.Head (support g) sourceRegistry.constructors interpretation)
      actualDemand.arguments declaration.head
    rw [original_arguments]
    exact .cons (.named ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 0],uses,uses,rfl,
      traced g .lower,traced g .upper⟩) .nil
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with same|later
    · cases same
      rfl
    · cases List.mem_singleton.mp later
      cases possible.1.2

noncomputable def selected {s : State} (g : Extends placedView s) {rank : Nat → Nat} (check : Ranked s rank) :
    Selected (support g) [] sourceRegistry interpretation waiting actualDemand declaration [requested] :=
  ⟨rootSlice g,keep,observedRoot,spans,[],exact_inputs done keep,fallback,targets,output keep,
    GeneralDeclarativeRepeatedTxn348.effective ▸ actual keep,
    literal (trans output_extends g),fun _ h => h,choice g check⟩

theorem rule {s : State} (g : Extends placedView s) {rank : Nat → Nat} (check : Ranked s rank) :
    Rule (support g) [] sourceRegistry interpretation waiting actualDemand (.selected declaration.id [requested]) :=
  .whole (selected g check)

end Yulang.GeneralDeclarativeRepeatedRoot348
