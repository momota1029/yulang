import Yulang.GeneralDeclarativeWithheldInput343
import Yulang.GeneralDeclarativeRankedBridge343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeclarativeOriginSplit343
open GeneralDeclarativeWithheldReceipt343 (withheld)
open GeneralDeclarativeCurrentWorld343 (now grows rank current_rank)
open GeneralDeclarativeCurrentOrigins343 (ChildReceipt)
open GeneralDeclarativeFrameShape343 (output_ordinary childRows)
open GeneralDeclarativePlacement343 (rows symbolic view)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child output fallback targets)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand original_arguments)
open GeneralDeclarativeVersionedRootShape342 (spans uses)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeInitialRoot343 (anchored)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (from_source restriction backed_iff)
open GeneralDeclarativeGrowth327 (trans facts)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeTaggedElection340 (Election Head)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

theorem still_observed : publicRow ∈ (restriction withheld).equations :=
  from_source _ (.inl ⟨anchored,rfl⟩)

def slice : Slice withheld :=
  ⟨observedRoot,GeneralDeclarativeInitialRoot343.support (fun _ => False),
    trans GeneralDeclarativeFrameShape343.grows grows,
    ⟨(by intro _ h; cases h),(by intro _ h; cases h), fun row member => by
      obtain ⟨_,fromHere,_⟩ := (backed_iff _ _).mp member
      rw [GeneralDeclarativeInitialRoot343.origin_unique fromHere.1]
      exact still_observed⟩⟩

theorem traced (mode : Mode) :
    Trace (restriction withheld) mode 0 (.nominal 0 [.variable 0,.variable 1]) uses :=
  Trace.nominal (args := [2,2]) (alias_refl _) still_observed (.cons .capture (.cons .capture .nil))

theorem root_still_elected : Election withheld sourceRegistry interpretation waiting actualDemand declaration := by
  refine ⟨?_,⟨rank,current_rank⟩,fun ⟨_,_,absent⟩ => absent,?_,?_⟩
  · intro a here
    rw [original_arguments] at here
    cases List.mem_singleton.mp here
    exact .inl ⟨_,knows_row still_observed rfl⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,?_⟩
    change All₂ (Head withheld sourceRegistry.constructors interpretation) actualDemand.arguments declaration.head
    rw [original_arguments]
    exact .cons (.named ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 1],uses,uses,rfl,
      traced .lower,traced .upper⟩) .nil
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with yes|tail
    · cases yes
      rfl
    · cases List.mem_singleton.mp tail
      cases possible.1.2

noncomputable def localWitness : Selected withheld [] sourceRegistry interpretation waiting actualDemand declaration [child kept] :=
  ⟨slice,kept,observedRoot,spans,[],GeneralDeclarativeInitialRoot343.exact_inputs (fun _ => False) kept,
    fallback,targets,output kept,GeneralDeclarativeOrdinary343.actual kept,literal (trans (facts _ rows) grows),
    fun _ h => h,root_still_elected⟩

/-- With completion authority withheld but old ordinary constraints
unaltered, the independently authored root still has its exact local
proposal. Its actual child no longer has a positive witness. There
is no claim that this counterfactual is a run of the executor. -/
theorem independent :
    Rule withheld [] sourceRegistry interpretation waiting actualDemand (.selected declaration.id [child kept]) ∧
    ∀ key children, ¬ Rule withheld [] sourceRegistry interpretation waiting (child kept) (.selected key children) :=
  ⟨.whole localWitness,GeneralDeclarativeWithheldReceipt343.cannot_use_truth_to_select⟩

end Yulang.GeneralDeclarativeOriginSplit343
