import Yulang.GeneralDeclarativeWitnessTypedFixture354
import Yulang.GeneralDeclarativeWitnessTypedSound354

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralDeclarativeWitnessTypedModel354
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool payload)
open GeneralDeclarativeWitnessTypedFixture354 (problem data test accepted writtenRow)
open GeneralDeclarativeWitnessTypedChild354 (Wire Linked decode physical_target)
open GeneralDeclarativeWitnessTypedSound354 (released_type_at_actual_center childView both)
open GeneralDeclarativeWitnessCovariantOrigin353 (View)
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

def supportedEquations : List Equation := [⟨7,eInt⟩,⟨8,eBool⟩,payload,⟨6,.variable 9⟩]

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) &&
  s.equations.all (fun e => decide (e ∈ supportedEquations))

theorem real_state_checked : (data.map fun (s,_) => covers s).getD false = true := by decide +kernel

theorem model_fits {s : State} {sign : Wire}
    (got : data = some (s,sign)) : Models s model := by
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
    rcases literal with rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem inhabited :
    ∃ (s : State) (w : Wire) (a : Linked problem s w),
      data = some (s,w) ∧ Models s model ∧
      a.receiver.facts.arg.center = a.emitted.atWrite.demand.target ∧
      (∃ named : View, childView a model a.receiver.facts.arg.center = some named ∧
        named.tag = a.emitted.atWrite.typed.tag ∧ named.box = a.emitted.atWrite.typed.box) ∧
      (∀ e ∈ GeneralDeclarativeWitnessTypedOutput354.ordinary w.writer.trace,Holds model e) ∧
      ∀ e ∈ w.child.outputRows,Holds model e := by
  have testOK := accepted
  unfold test at testOK
  cases got : data with
  | none => simp [got] at testOK
  | some pair =>
    obtain ⟨s,w⟩ := pair
    have known : (decode problem s w).isSome = true := by simpa [got] using testOK
    cases ok : decode problem s w with
    | none => simp [ok] at known
    | some a =>
      have fit := model_fits got
      obtain ⟨view,named,tag,box,_⟩ := released_type_at_actual_center a model fit
      have full := both a model fit
      exact ⟨s,w,a,rfl,fit,physical_target a,⟨view,named,tag,box⟩,full.2.1,full.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessTypedModel354
