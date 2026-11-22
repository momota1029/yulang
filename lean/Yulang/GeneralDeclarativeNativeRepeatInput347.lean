import Yulang.GeneralDeclarativeNativeRepeatCompile347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralDeclarativeNativeRepeatInput347
open GeneralLiveCompoundRegistry316 (declaration sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeNativeRepeatStage347 (spans)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand original_arguments ready_iff)
open GeneralDeclarativeVersionedRootShape342 (point ranked level)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeInitialRoot343 (support source_backed)
open GeneralDeclarativeOrigins321 (backed_iff restriction)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)

abbrev uses : List Occurrence := [⟨0,.actual,2⟩,⟨0,.actual,2⟩]

theorem read_modes (done : Nat → Prop) (mode : GeneralNominalMaterialization.Mode) :
    Trace (restriction (support done)) mode 0 (.nominal 0 [.variable 0,.variable 0]) uses :=
  Trace.nominal (args := [2,2]) (alias_refl _) ((backed_iff _ publicRow).mpr (source_backed done))
    (.cons .capture (.cons .capture .nil))

/-- Both occurrences are derived independently from the actual
original source, and remain the same actual center name. The two
occurrences are not silently changed into C319's distinct binders. -/
theorem exact_inputs (done : Nat → Prop) (keep : List Nat) :
    Inputs (support done) sourceRegistry.constructors interpretation keep observedRoot
      actualDemand.arguments declaration.head observedRoot spans [] := by
  have grounded : Actual observedRoot sourceRegistry.constructors interpretation (support done) point
      (.app 0 [.var 0,.var 0]) spans :=
    ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 0],uses,
      rfl,read_modes done .actual,
      .cons ⟨rfl,rfl,point_bounded _ _⟩ (.cons ⟨rfl,rfl,point_bounded _ _⟩ .nil)⟩
  rw [original_arguments]
  exact .cons (.prior (.old (.named grounded))) .nil

theorem elected (done : Nat → Prop) :
    Election (support done) sourceRegistry interpretation GeneralDeclarativeVersionedChildWitness342.waiting
      actualDemand declaration := by
  refine ⟨(ready_iff _).mpr (source_backed done),⟨level,ranked⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,?_⟩
    change CommonRoleOutermostResolver.All₂
      (GeneralDeclarativeTaggedElection340.Head (support done) sourceRegistry.constructors interpretation)
      actualDemand.arguments declaration.head
    rw [original_arguments]
    exact .cons (.named ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 0],uses,uses,rfl,
      read_modes done .lower,read_modes done .upper⟩) .nil
  · intro alternative possible
    rcases List.mem_cons.mp possible.1.1 with here|last
    · cases here
      rfl
    · cases List.mem_singleton.mp last
      cases possible.1.2

end Yulang.GeneralDeclarativeNativeRepeatInput347
