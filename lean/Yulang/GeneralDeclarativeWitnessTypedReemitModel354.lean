import Yulang.GeneralDeclarativeWitnessTypedReemitFixture354
import Yulang.GeneralDeclarativeWitnessTypedReemitPayload354

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralDeclarativeWitnessTypedReemitModel354
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool payload)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem View)
open GeneralDeclarativeWitnessTypedRangeFixture354 (emitted)
open GeneralDeclarativeWitnessTypedReemitFixture354 (seed)
open GeneralDeclarativeWitnessCovariantFixture353 (wire)
open GeneralDeclarativeWitnessTypedForestFixture354 (head)
open GeneralDeclarativeWitnessTypedReemit354 (Wire Linked decode)
open GeneralDeclarativeWitnessTypedReemitPayload354 (Carry check exact_same_model)
open GeneralDeclarativeWitnessTypedPacket354 (Report)
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

def supportedEquations : List Equation := [⟨7,eInt⟩,⟨8,eBool⟩,payload,⟨6,.variable 9⟩,⟨10,.variable 9⟩]

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) &&
  s.equations.all (fun e => decide (e ∈ supportedEquations))

theorem real_state_checked : (emitted.map fun (s,_,_,_) => covers s).getD false = true := by decide +kernel

theorem model_fits {s : State} {actual : Problem} {top out : Report}
    (got : emitted = some (s,actual,top,out)) : Models s model := by
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

def carries : Bool :=
  (emitted.map (fun (s,_,top,r) =>
    ((decode seed s ⟨wire,top,head false,r⟩).map (fun a => (check a 0).isSome)).getD false)).getD false

theorem exact_receiver_output_is_whole : carries = true := by decide +kernel

theorem actual_chain_same_model :
    ∃ (s : State) (w : Wire) (a : Linked seed s w) (c : Carry a 0),
      Models s model ∧
      a.receiver.compiled.readFrom.arg.center = a.out.atWrite.demand.target ∧
      w.receiver.trace[0]? = some (.typed c.indexed.typed.row) ∧
      Equivalent (model c.indexed.typed.row.valueName).1
        (.union (model a.writer.output.source.anchor.first.valueName).1
                (model a.writer.output.source.anchor.last.valueName).1) := by
  have testOK := exact_receiver_output_is_whole
  unfold carries at testOK
  cases got : emitted with
  | none => rw [got] at testOK; cases testOK
  | some tuple =>
    obtain ⟨s,p,top,r⟩ := tuple
    let w : Wire := ⟨wire,top,head false,r⟩
    change ((emitted.map fun (s,_,top,r) =>
      ((decode seed s ⟨wire,top,head false,r⟩).map (fun a => (check a 0).isSome)).getD false)).getD false = true at testOK
    have present : ((decode seed s w).map (fun a => (check a 0).isSome)).getD false = true := by simpa [got,w] using testOK
    cases accepted : decode seed s w with
    | none => simp [accepted] at present
    | some a =>
      cases reported : check a 0 with
      | none => simp [accepted,reported] at present
      | some c =>
        have fit := model_fits got
        have fact := exact_same_model c model fit
        exact ⟨s,w,a,c,fit,GeneralDeclarativeWitnessTypedReemit354.released_physical_center a,fact.2.1,fact.2.2.2⟩

def noPublish : Bool :=
  (emitted.map (fun (s,_,top,r) =>
    ((decode seed s ⟨wire,top,head false,r⟩).map (fun a =>
      (GeneralDeclarativeWitnessTypedReemit354.typedView a model 10).isNone)).getD false)).getD false

theorem actual_reemission_not_published_in_consumer_scope : noPublish = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedReemitModel354
