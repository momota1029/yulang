import Yulang.GeneralDeclarativeWitnessGrandchildTreeFixture355

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralDeclarativeWitnessGrandchildModel355
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem View bill)
open GeneralDeclarativeWitnessGrandchildFixture355 (data plan)
open GeneralDeclarativeWitnessGrandchildSeed355 (producer seed)
open GeneralDeclarativeWitnessGrandchildContinuity355 (realInterval)
open GeneralDeclarativeWitnessGrandchildTree355 (Checked read ordered all_writes)
open GeneralDeclarativeWitnessGrandchildTreeFixture355 (declared test actual_three_levels)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessTypedReemit354 (Wire Linked decode)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open CommonNominalFullCarrier (Equivalent Ty Subtype subtype_refl)

def int : Ty := .base .int
def bool : Ty := .base .bool
def whole : Ty := .union int bool

inductive Kind where
  | integer | boolean | merged
  deriving DecidableEq

def kind (n : Nat) : Kind := if n = 7 then .integer else if n = 8 then .boolean else .merged

def value : Kind → Ty
  | .integer => int
  | .boolean => bool
  | .merged => whole

def model : Assignment := fun n => (value (kind n),Common.rowEmpty)

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var r) => decide (kind l = kind r)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (h : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l r =>
    cases l <;> cases r <;> try cases h
    rename_i l r
    have eq : kind l = kind r := of_decide_eq_true h
    change Subtype (value (kind l)) (value (kind r))
    rw [eq]
    exact subtype_refl _
  | rowLe _ _ => cases h

def supportedEquations : List Equation := [⟨7,eInt⟩,⟨8,eBool⟩,bill 10 7 8,⟨6,.variable 10⟩,⟨10,.variable 10⟩]

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) &&
  s.equations.all (fun e => decide (e ∈ supportedEquations))

theorem real_state_checked : ((data 10).map fun (s,_,_) => covers s).getD false = true := by decide +kernel

theorem model_fits {s : State} {top : Wire} {out : GeneralDeclarativeWitnessGrandchild355.Wire}
    (got : data 10 = some (s,top,out)) : Models s model := by
  have verified := real_state_checked
  rw [got] at verified
  have ⟨facts,erows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers s = true from verified)
  have ⟨atoms,intervals⟩ := GeneralDeclarativeWitnessProblem349.splitAnd facts
  have noIntervals := List.isEmpty_iff.mp intervals
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a used
    exact atom_sound a (List.all_eq_true.mp atoms _ used)
  · intro pair used
    rw [noIntervals] at used
    cases used
  · intro e used
    have literal := of_decide_eq_true (List.all_eq_true.mp erows _ used)
    simp only [supportedEquations,List.mem_cons,List.not_mem_nil,or_false] at literal
    rcases literal with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem actual_three_level_models :
    ∃ (s : State) (w : Wire) (c : GeneralDeclarativeWitnessGrandchild355.Wire)
      (a : Linked (seed 10) s w) (b : Checked a plan c declared),
      Models s model ∧
      b.last.results.facts.arg.center = b.last.released.body.indexed.demand.target ∧
      declared.result = .selected (GeneralDeclarativeWitnessGrandchildTree355.dictionary b.last) ∧
      w.receiver.trace.map GeneralDeclarativeWitnessTypedOutput354.Write.target =
        a.child.outputs.map GeneralSourceState.Output.target ∧
      ∃ v, realInterval v a.receiver.compiled.readFrom.arg w.receiverHead.center.box ∧
        realInterval v b.last.results.facts.arg c.head.center.box := by
  have succeeds := actual_three_levels
  unfold test at succeeds
  cases got : data 10 with
  | none => rw [got] at succeeds; cases succeeds
  | some row =>
    obtain ⟨s,w,c⟩ := row
    have tested : ((decode (seed 10) s w).map
      (fun a => (read a plan c declared).isSome)).getD false = true := by simpa [got] using succeeds
    cases mid : decode (seed 10) s w with
    | none => rw [mid] at tested; cases tested
    | some a =>
      cases after : read a plan c declared with
      | none => simp [mid,after] at tested
      | some b =>
        have fit := model_fits got
        have clean := all_writes b model fit
        exact ⟨s,w,c,a,b,fit,GeneralDeclarativeWitnessGrandchild355.exact_target b.last,
          (ordered b).2.1,clean.2.1,clean.2.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessGrandchildModel355
