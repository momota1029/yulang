import Yulang.GeneralDeclarativeStoppedDepthView341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 15500000
namespace Yulang.GeneralDeclarativeStoppedDepthWitness341
open GeneralDictionaryOutputDepth252 (sourceRegistry roles root interpretation declaration source_checked coverage)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralDeclarativeStoppedDepthView341 (inputRow outRow before final requested used keep fall targets waiting support authored)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTaggedElection340 (Ranked Election tests Head)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeCurrentReceipt330 (Receipt literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeWitnessHead334 (full)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeOutputSource323 (Declared)
open CommonRoleOutermostResolver (Classify All₂)

def level (n : Nat) : Nat := if n = 3 then 2 else if n = 2 then 1 else 0
theorem declared : Declared sourceRegistry requested := by
  intro output present
  cases List.mem_singleton.mp present
  exact ⟨none,rfl⟩

abbrev extra : List (PresenceNormalForm.Atom Nat) :=
  [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2),
   .tyLe (.var 4) (.var 2),.tyLe (.var 2) (.var 4),
   .tyLe (.var 5) (.var 2),.tyLe (.var 2) (.var 5),
   .tyLe (.var 4) (.var 2),.tyLe (.var 2) (.var 5)]
noncomputable abbrev compiled : State :=
  ⟨⟨before.normal.ordinary ++ extra,[]⟩,[inputRow,outRow]⟩

theorem printed :
    compileBody sourceRegistry interpretation requested declaration before used keep fall targets =
      some (compiled,[]) := by
  with_unfolding_all rfl

theorem old_grows : GeneralDeclarativeGrowth327.Extends before compiled :=
  ⟨fun _ h => List.mem_append_left _ h,fun _ h => h,
    fun _ h => List.mem_append_left [outRow] h⟩

theorem expanded_grows : GeneralDeclarativeGrowth327.Extends final compiled :=
  ⟨fun _ h => List.mem_append_left _ h,fun _ h => h,fun _ h => h⟩

noncomputable def current (done : Nat → Prop) : GeneralDeclarativeOrigins321.Supported compiled done :=
  GeneralDeclarativeObserverGrowth330.preserve (support done) expanded_grows

noncomputable def initial (done : Nat → Prop) : GeneralDeclarativeOrigins321.Supported before done :=
  GeneralStoppedLower335.original GeneralDeclarativeStoppedDepthView341.source before (fun _ h => h) done

theorem keeps (done : Nat → Prop) :
    GeneralDeclarativeGrowth327.Extends
      (GeneralDeclarativeOrigins321.restriction (initial done))
      (GeneralDeclarativeOrigins321.restriction (current done)) := by
  refine ⟨old_grows.constraints,old_grows.intervals,?_⟩
  intro e member
  obtain ⟨_,⟨source,_⟩,_⟩ := (GeneralDeclarativeOrigins321.backed_iff (initial done) _).mp member
  cases List.mem_singleton.mp source
  exact (GeneralDeclarativeObserverGrowth330.sources_grow (support done) expanded_grows).equations (authored done)

def extendedLevel (n : Nat) := if n = 4 ∨ n = 5 then level 2 else level n

theorem compiled_check : compiled.normal.ordinary.all
  (fun v => match v with
    | .tyLe (.var a) (.var b) => decide (extendedLevel a ≤ extendedLevel b)
    | _ => true) = true := by decide +kernel

theorem expanded_ranked : Ranked compiled extendedLevel := by
  refine ⟨?_,?_,?_⟩
  · intro a b path
    induction path with
    | interval placed => cases placed
    | constraint placed => exact of_decide_eq_true (List.all_eq_true.mp compiled_check _ placed)
    | refl => exact Nat.le_refl _
    | trans _ _ x y => exact Nat.le_trans x y
  · intro a b seen
    change (⟨a,.variable b⟩ : Equation) ∈ [inputRow,outRow] at seen
    rcases List.mem_cons.mp seen with no|last
    · cases no
    · cases List.mem_singleton.mp last
  · intro row seen n occurs _
    change row ∈ [inputRow,outRow] at seen
    rcases List.mem_cons.mp seen with rfl|last
    · have exact : n = 0 := List.mem_singleton.mp occurs
      subst n
      decide +kernel
    · cases List.mem_singleton.mp last
      have exact : n = 2 := List.mem_singleton.mp occurs
      subst n
      decide +kernel

theorem current_election (done : Nat → Prop) :
    Election (current done) sourceRegistry interpretation waiting requested declaration := by
  refine ⟨?_,⟨extendedLevel,expanded_ranked⟩,fun ⟨_,_,no⟩ => no,?_,?_⟩
  · intro a seen
    cases List.mem_singleton.mp seen
    exact .inl ⟨_,knows_row ((GeneralDeclarativeObserverGrowth330.sources_grow (support done) expanded_grows).equations (authored done)) rfl⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,.cons (.named ?_) .nil⟩
    exact ⟨point_bounded _ _,_,_,_,rfl,.capture,.capture⟩
  · intro other visible
    exact congrArg GeneralDeclarations.Declaration.id (List.mem_singleton.mp visible.1.1)

theorem actual_input (done : Nat → Prop) :
    GeneralDeclarativeStableTrace329.Actual before sourceRegistry.constructors interpretation (initial done)
      (point 2) (.var 0) used := by
  refine ⟨point_bounded _ _, .variable 0, [⟨0,.actual,2⟩], rfl, .capture, ?_⟩
  exact .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil

theorem inputs (done : Nat → Prop) :
    Inputs (initial done) sourceRegistry.constructors interpretation keep before requested.arguments
      declaration.head before used [] := by
  change Inputs (initial done) sourceRegistry.constructors interpretation keep before [point 2] [.var 0] before (used ++ []) ([] ++ [])
  exact .cons (.prior (.old (.named (actual_input done)))) .nil

noncomputable def witness (done : Nat → Prop) :
    Selected (current done) [] sourceRegistry interpretation waiting requested declaration [] where
  slice := ⟨before,initial done,old_grows,keeps done⟩
  keep := keep
  named := before
  spans := used
  reads := []
  input := inputs done
  fallback := fall
  targets := targets
  ordinary := compiled
  compiler := printed
  receipt := literal (reflexive _)
  retained := fun _ h => h
  elected := current_election done

end Yulang.GeneralDeclarativeStoppedDepthWitness341
