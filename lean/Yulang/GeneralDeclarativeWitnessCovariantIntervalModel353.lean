import Yulang.GeneralDeclarativeWitnessCovariantIntervalFixture353
import Yulang.GeneralDeclarativeWitnessCovariantCarrier352

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralDeclarativeWitnessCovariantIntervalModel353
open GeneralDeclarativeWitnessCovariantIntervalFixture353 (problem wire data upperEq test accepted run)
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool payload out)
open GeneralDeclarativeWitnessCovariantInterval353 (Checked decode typed_interval exact_write_targets)
open GeneralDeclarativeWitnessCovariantOrigin353 (HasView Valuation assigned)
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
  | integer | boolean | merged | wider
  deriving DecidableEq

def kind (n : Nat) : Kind := if n = 7 then .integer else if n = 8 then .boolean else if n = 10 then .wider else .merged

def value : Kind → Ty
  | .integer => int
  | .boolean => bool
  | .merged => whole
  | .wider => .union whole (.base .unit)

def model : Assignment := fun n => (value (kind n),Common.rowEmpty)

def allowed (a b : Kind) : Bool :=
  decide (a = b ∨ (a = .integer ∧ b = .merged) ∨ (a = .merged ∧ b = .wider))

theorem allowed_model {a b : Kind} (yes : allowed a b = true) : Subtype (value a) (value b) := by
  rcases of_decide_eq_true yes with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact subtype_refl _
  · exact ((CommonNominalFullCarrier.common_union_is_join int bool whole).mp (subtype_refl _)).1
  · exact ((CommonNominalFullCarrier.common_union_is_join whole (.base .unit) (.union whole (.base .unit))).mp
      (subtype_refl _)).1

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var r) => allowed (kind l) (kind r)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (h : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l r =>
    cases l <;> cases r <;> try cases h
    exact allowed_model h
  | rowLe _ _ => cases h

def supportedEquations : List Equation := [⟨7,eInt⟩,⟨8,eBool⟩,payload,upperEq] ++ out

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
    rcases literal with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

def valuation : Valuation
  | 30 => some ⟨13,0,(assigned model 7).1⟩
  | 31 => some ⟨13,0,(assigned model 8).1⟩
  | 20 => some ⟨13,0,(assigned model 9).1⟩
  | 11 => some ⟨13,0,(assigned model 7).1⟩
  | 21 => some ⟨13,0,(assigned model 10).1⟩
  | _ => none

theorem actual_rows : ∀ e ∈ problem.rows, HasView model valuation e := by
  intro e used
  simp only [problem,GeneralDeclarativeWitnessCovariantFixture353.rows,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl|rfl <;> exact ⟨_,rfl,rfl,rfl,Common.equivalent_refl _⟩

theorem lower_strict : ¬Equivalent (model 7).1 (model 9).1 :=
  GeneralDeclarativeWitnessCovariantCarrier352.not_left_payload

theorem genuine_nonpoint :
    ∃ (s : State) (sign : GeneralDeclarativeWitnessCompiler350.Wire) (a : Checked problem wire s sign),
      data = some (s,sign) ∧ Models s model ∧
      (∃ lo c hi : GeneralDeclarativeWitnessCovariantOrigin353.View,
        valuation a.facts.arg.lower = some lo ∧ valuation a.facts.arg.center = some c ∧
        valuation a.facts.arg.upper = some hi ∧
        CommonDeclaredNominalInspection.DeclaredSubtype
          (GeneralDeclarativeWitnessCovariantMetadata353.table wire.center.box)
          (GeneralDeclarativeWitnessCovariantViews353.View.head lo)
          (GeneralDeclarativeWitnessCovariantViews353.View.head c) ∧
        CommonDeclaredNominalInspection.DeclaredSubtype
          (GeneralDeclarativeWitnessCovariantMetadata353.table wire.center.box)
          (GeneralDeclarativeWitnessCovariantViews353.View.head c)
          (GeneralDeclarativeWitnessCovariantViews353.View.head hi)) ∧
      sign.outputRows.map Equation.left = [5,6] ∧
      (∀ e ∈ sign.outputRows,Holds model e) := by
  have shown := accepted
  unfold test at shown
  cases got : data with
  | none => simp [got] at shown
  | some item =>
    obtain ⟨s,sign⟩ := item
    have checked : (decode problem wire s sign).isSome = true := by simpa [got] using shown
    cases yes : decode problem wire s sign with
    | none => simp [yes] at checked
    | some a =>
      have fits := model_fits got
      have previous := GeneralDeclarativeGrowth327.restrict
        ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp a.kept) model fits
      obtain ⟨l,c,h,atLower,atCenter,atUpper,_,lower,upper⟩ := typed_interval a.facts model valuation previous actual_rows
      have writes := (exact_write_targets a model fits).2
      exact ⟨s,sign,a,rfl,fits,⟨l,c,h,atLower,atCenter,atUpper,lower,upper⟩,writes⟩

end Yulang.GeneralDeclarativeWitnessCovariantIntervalModel353
