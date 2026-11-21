import Yulang.GeneralDeclarativeStableReplay329
import Yulang.GeneralDeclarativeRepeatedSource323

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeStableCrossSource329
open GeneralDeclarativeRepeatedSource323 (registry parent child goal a b nominalCode scalar pat)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeStableTrace329 (Actual Located)
open GeneralDeclarativeStableHybrid329 (Source Certified Task certify replay_inputs)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeOpaquePlan328 (Plan Read Shape)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty nominal subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeRepeat320 (int)

abbrev oldRows : List Equation :=
  [⟨0,nominalCode 3⟩,⟨1,nominalCode 3⟩,⟨2,nominalCode 4⟩,⟨10,nominalCode 7⟩,
    ⟨12,nominalCode 8⟩,⟨3,scalar⟩,⟨4,.variable 3⟩,⟨8,.variable 7⟩]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2),(10,11),(11,12)]⟩,oldRows⟩
def supported (done : Nat → Prop) : Supported initial done :=
  ⟨fun e o => e ∈ oldRows ∧ o = .source,fun h => h.1⟩
theorem allowed (done : Nat → Prop) {e : Equation} (found : e ∈ oldRows) :
    e ∈ (restriction (supported done)).equations :=
  from_source _ ⟨found,rfl⟩

theorem range_a : Bounds initial a :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
theorem range_b : Bounds initial b :=
  ⟨.interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    .interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem observed (done : Nat → Prop) :
    Actual initial registry.constructors interp (supported done) a pat [(0,point 3)] := by
  refine ⟨range_a,nominalCode 0,[⟨0,.actual,3⟩],rfl,?_,?_⟩
  · exact .nominal (args := [3]) (alias_refl _)
      (allowed done (show (⟨1,nominalCode 3⟩ : Equation) ∈ oldRows from
        List.mem_cons_of_mem _ List.mem_cons_self)) (.cons .capture .nil)
  · exact .cons ⟨rfl,rfl,.refl _,.refl _⟩ .nil

theorem reads_pair (done : Nat → Prop) :
    Source initial registry.constructors interp (supported done) goal.arguments parent.head := by
  refine .actual (observed done) (.concealed ⟨range_b,nominalCode 0,[⟨0,.actual,7⟩],
    [⟨0,.actual,8⟩],rfl,?_,?_⟩ ?_ .nil)
  · exact .nominal (args := [7]) (alias_refl _) (allowed done (show
      (⟨10,nominalCode 7⟩ : Equation) ∈ oldRows by simp [oldRows])) (.cons .capture .nil)
  · exact .nominal (args := [8]) (alias_refl _) (allowed done (show
      (⟨12,nominalCode 8⟩ : Equation) ∈ oldRows by simp [oldRows])) (.cons .capture .nil)
  · intro code isCode
    change some (nominalCode 0) = some code at isCode
    cases Option.some.inj isCode
    exact .invariant .capture

abbrev tasks := [Task.actual [(0,point 3)],Task.project b (.invariant 0 7 8 (.capture 0))]
abbrev keep := demandNames goal
abbrev actual := GeneralDeclarativeStableHybrid329.run keep initial tasks
abbrev spans := [(0,point 3),(0,point 7)]

theorem named : Certified initial registry.constructors interp goal.arguments parent.head tasks := by
  obtain ⟨_,_,decl,trace,spots⟩ := (observed (fun _ => False)).reads
  obtain ⟨read,limits⟩ := GeneralDeclarativeStableTrace329.from_trace range_a decl trace spots
  exact .actual read limits (.project range_b rfl (.invariant
    (.row (by simp [oldRows])) (.row (by simp [oldRows])) .capture) .nil)

theorem real_spans : actual.spans = spans := rfl
theorem actual_rows : actual.state.equations = oldRows ++ [⟨11,nominalCode 7⟩] := rfl
theorem no_original_eleven : ¬ ∃ exp, (⟨11,exp⟩ : Equation) ∈ initial.equations := by
  intro h
  obtain ⟨exp,there⟩ := h
  simp only [oldRows,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with x|x|x|x|x|x|x|x <;> have contradiction := congrArg Equation.left x <;> cases contradiction

theorem real_heads : Heads actual.state registry.constructors interp goal.arguments parent.head spans :=
  (replay_inputs keep named).2.1
theorem real_ranges : ∀ s ∈ spans, Bounds actual.state s.2 :=
  (replay_inputs keep named).2.2

def assignment (second : Ty) : Assignment := fun n =>
  (if n ≤ 2 then nominal 0 [.inl int] else if 10 ≤ n ∧ n ≤ 12 then nominal 0 [.inl second]
    else if n = 7 ∨ n = 8 then second else int,Common.rowEmpty)

theorem actual_model (second : Ty) : Models actual.state (assignment second) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro span found
    change _ ∈ [(0,1),(1,2),(10,11),(11,12)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with x|x|x|x <;> cases x <;> exact subtype_refl _
  · intro row found
    rw [actual_rows] at found
    simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with x|x|x|x|x|x|x|x|x <;> cases x <;> exact eqv_refl _

end Yulang.GeneralDeclarativeStableCrossSource329
