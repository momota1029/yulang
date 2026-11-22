import Yulang.GeneralDeclarativeWitnessCovariantFixture353
import Yulang.GeneralDeclarativeWitnessCovariantViews353

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralDeclarativeWitnessCovariantModel353
open GeneralDeclarativeWitnessCovariantFixture353 (problem wire data stage eInt eBool payload out rows test run actual_accept)
open GeneralDeclarativeWitnessCovariantCompiler353 (Checked check confirmed retained)
open GeneralDeclarativeWitnessCovariantOrigin353 (ModelsAt Valuation assigned)
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

def supportedEquations : List Equation := [⟨7,eInt⟩,⟨8,eBool⟩,payload] ++ out

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) &&
  s.equations.all (fun e => decide (e ∈ supportedEquations))

theorem real_state_checked : (data.map fun (s,_) => covers s).getD false = true := by decide +kernel

theorem model_fits {s : State} {sign : GeneralDeclarativeWitnessCompiler350.Wire}
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
    simp only [supportedEquations,out,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at literal
    rcases literal with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

def valuation : Valuation
  | 30 => some ⟨13,0,(assigned model 7).1⟩
  | 31 => some ⟨13,0,(assigned model 8).1⟩
  | 20 => some ⟨13,0,(assigned model 9).1⟩
  | _ => none

theorem view_fits {s : State} {sign} (a : Checked problem wire s sign) (fit : Models s model) :
    ModelsAt problem model valuation := by
  refine ⟨retained a model fit,?_⟩
  intro item used
  change item ∈ rows at used
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl <;> exact ⟨_,rfl,rfl,rfl,Common.equivalent_refl _⟩

theorem literal_children :
    (run.map (fun f => decide (f.kids.map printDemand = [(3,[(32,9,33)],[]),(4,[(34,9,35)],[])]))).getD false =
      true := by decide +kernel

/-- A genuine compiler execution and independent semantic model inhabit
the new typed certificate. All preserved ordinary captures and fixed
output writes use one model; the typed nominal boundary is explicit. -/
theorem nonvacuous :
    ∃ (s : State) (sign : GeneralDeclarativeWitnessCompiler350.Wire) (_a : Checked problem wire s sign),
      data = some (s,sign) ∧ Models s model ∧ ModelsAt problem model valuation ∧
      sign.children = [(3,[(32,9,33)],[]),(4,[(34,9,35)],[])] ∧
      sign.outputRows = out ∧ (∀ e ∈ sign.outputRows,Holds model e) := by
  cases result : data with
  | none =>
    have h := actual_accept
    simp [test,result] at h
  | some outPair =>
    obtain ⟨s,sign⟩ := outPair
    have ok := actual_accept
    unfold test at ok
    rw [result] at ok
    have atFixture : (check problem wire s sign).isSome = true := ok
    cases checked : check problem wire s sign with
    | none => simp [checked] at atFixture
    | some a =>
      have fit := model_fits result
      have current := confirmed a model fit
      have printed :
          (data.map (fun (_,p) => decide (p.children = [(3,[(32,9,33)],[]),(4,[(34,9,35)],[])] ∧
            p.outputRows = out))).getD false = true := by decide +kernel
      rw [result] at printed
      obtain ⟨ordered,rows⟩ := of_decide_eq_true (show decide
        (sign.children = [(3,[(32,9,33)],[]),(4,[(34,9,35)],[])] ∧ sign.outputRows = out) = true from printed)
      exact ⟨s,sign,a,rfl,fit,view_fits a fit,ordered,rows,current.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantModel353
