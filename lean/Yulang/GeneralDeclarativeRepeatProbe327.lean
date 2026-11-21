import Yulang.GeneralDeclarativeRepeatState327
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativePairNames326 (first second)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeGrowth327 (Extends trans facts fits)

theorem normalized_rows : clausesState.equations = presentRows ++
    [⟨12,.variable 3⟩,⟨13,.variable 7⟩,⟨14,.variable 4⟩,⟨15,.variable 9⟩,
     ⟨16,.variable 7⟩,⟨17,.variable 10⟩] ++ inputRows := rfl

theorem base_row {e : Equation} (listed : e ∈ presentRows ++ inputRows) :
    e ∈ clausesState.equations := by
  rw [normalized_rows]
  rcases List.mem_append.mp listed with source|generated
  · exact List.mem_append_left _ (List.mem_append_left _ source)
  · exact List.mem_append_right _ generated

def source (done : Nat → Prop) : Supported clausesState done :=
  ⟨fun e o => e ∈ presentRows ++ inputRows ∧ o = .source,fun h => base_row h.1⟩

abbrev supported (done : Nat → Prop) := emit (emit (source done) 1 [rootRow]) 2 [childRow]

theorem authored (done : Nat → Prop) {e : Equation} (listed : e ∈ presentRows ++ inputRows) :
    e ∈ (restriction (supported done)).equations :=
  from_source _ (.inl (.inl ⟨listed,rfl⟩))

theorem root_interval : Bounds result arg :=
  fits (show Extends initial result from
    ⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ h)),
      fun _ h => List.mem_append_left _ (List.mem_append_left _ (base_row (List.mem_append_left _ h)))⟩) root_bounds

theorem child_interval : Bounds result argC :=
  fits (trans (facts clausesState [rootRow]) (facts _ [childRow]))
    (GeneralDeclarativeFreshInputs325.names_bounded (e := compoundCode) rfl)

theorem center_of_merge : Bounds result combined :=
  fits (show Extends mergedState result from
    ⟨fun _ h => h,fun _ h => List.mem_append_left _ h,fun _ h => List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ h))⟩) aggregate.1

theorem root_support (done : Nat → Prop) : Ready (supported done) root := by
  intro a listed
  cases List.mem_singleton.mp listed
  exact ⟨_,knows_row (authored done (List.mem_append_left _ (show (⟨0,low⟩ : Equation) ∈ presentRows from
    List.mem_cons_self))) rfl⟩

theorem child_source (done : Nat → Prop) :
    (⟨20,.nominal 0 [.variable 13]⟩ : Equation) ∈ (restriction (supported done)).equations := by
  apply authored done
  apply List.mem_append_right
  rw [input_exact]
  exact List.mem_cons_self

theorem child_support (done : Nat → Prop) : Ready (supported done) child := by
  intro a listed
  cases List.mem_singleton.mp listed
  exact ⟨_,knows_row (child_source done) rfl⟩

theorem root_matches (done : Nat → Prop) : HeadMatches (restriction (supported done)) reg.constructors interp root impl := by
  refine .cons ⟨root_interval,headCode,[⟨0,.lower,3⟩,⟨0,.lower,9⟩],[⟨0,.upper,4⟩,⟨0,.upper,10⟩],rfl,?_,?_⟩ .nil
  · exact .primitive (args := [3,9]) (alias_refl _) (authored done (List.mem_append_left _
      (show (⟨0,low⟩ : Equation) ∈ presentRows from List.mem_cons_self))) (.cons .capture (.cons .capture .nil))
  · exact .primitive (args := [4,10]) (alias_refl _) (authored done (List.mem_append_left _
      (show (⟨2,high⟩ : Equation) ∈ presentRows from List.mem_cons_of_mem _ List.mem_cons_self)))
      (.cons .capture (.cons .capture .nil))

theorem child_matches (done : Nat → Prop) : HeadMatches (restriction (supported done)) reg.constructors interp child
    GeneralDeclarativeExampleSource320.leaf :=
  .cons ⟨child_interval,.variable 0,[⟨0,.lower,20⟩],[⟨0,.upper,22⟩],rfl,.capture,.capture⟩ .nil

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (supported done)) reg.constructors interp,
    fun d impl => ¬HeadMatches (restriction (supported done)) reg.constructors interp d impl⟩

end Yulang.GeneralDeclarativeRepeatProbe327
