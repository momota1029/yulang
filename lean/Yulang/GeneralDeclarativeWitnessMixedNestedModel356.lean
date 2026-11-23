import Yulang.GeneralDeclarativeWitnessMixedLedgerFixture356
import Yulang.GeneralDeclarativeTaggedFixtureModel340
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 55000
set_option maxHeartbeats 68000000
namespace Yulang.GeneralDeclarativeWitnessMixedNestedModel356
open GeneralDeclarativeWitnessMixedReal356 (sourceEquations problem)
open GeneralDeclarativeWitnessMixedNestedFixture356 (Data data checkedRoot authors)
open GeneralDeclarativeWitnessMixedLedgerFixture356 (test packet exactLedger full_preorder_ledger_is_real)
open GeneralDeclarativeWitnessMixedLedger356 (Accepted read returned_sound Meaning)
open GeneralDeclarativeWitnessRecursiveSound356 (Evident)
open GeneralDeclarativeWitnessRecursiveTree356 (dictionary)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessCovariantFixture353 (eInt eBool)
open GeneralDeclarativeTaggedFixtureModel340 (int boolean actualRoot entire)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment variant_merge)
open CommonNominalFullCarrier (Ty variant Subtype subtype_refl Equivalent)
open CommonRoleOutermostResolver (All₂)

inductive Kind where
  | left | right | tagged | payload
  deriving DecidableEq

def kind (n : Nat) : Kind :=
  if n = 7 then .left else if n = 8 then .right else if 80 ≤ n then .payload else .tagged

def ty : Kind → Ty
  | .left => variant 7 int
  | .right => variant 7 boolean
  | .tagged => actualRoot
  | .payload => entire

def model : Assignment := fun n => (ty (kind n),Common.rowEmpty)

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var h) => decide (kind l = kind h)
  | _ => false

theorem atom_sound (e : PresenceNormalForm.Atom Nat) (ok : atomOK e = true) :
    e.Holds CommonNominalFullCarrier.model model := by
  cases e with
  | tyLe l r =>
    cases l <;> cases r <;> try cases ok
    rename_i l r
    have same : kind l = kind r := of_decide_eq_true ok
    change Subtype (ty (kind l)) (ty (kind r))
    rw [same]
    exact subtype_refl _
  | rowLe _ _ => cases ok

def rigid : List Equation := sourceEquations ++
  [⟨60,.variable 10⟩,⟨6,.variable 10⟩,
  ⟨10,.variant 7 (.variable 86)⟩,⟨60,.variant 7 (.variable 86)⟩,
  ⟨70,.variable 10⟩,⟨10,.variant 7 (.variable 126)⟩,⟨70,.variant 7 (.variable 126)⟩]

def payload : Expr := .join eInt eBool

local instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (GeneralDeclarativeWitnessLiteral349.eqExpr a b = true)
    (GeneralDeclarativeWitnessLiteral349.eq_expr a b)

def eqOK (e : Equation) : Bool := decide (e ∈ rigid) ||
  decide (80 ≤ e.left ∧ e.right = payload)

theorem rigid_sound {e : Equation} (inside : e ∈ rigid) : Holds model e := by
  simp only [rigid,sourceEquations,List.mem_cons,List.not_mem_nil,List.mem_append,or_false] at inside
  rcases inside with ((rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl))
  · exact eqv_refl _
  · exact eqv_refl _
  · exact eqv_refl _
  · exact eqv_refl _
  · exact eqv_refl _
  · exact variant_merge 7 int boolean
  · exact variant_merge 7 int boolean
  · exact eqv_refl _
  · exact variant_merge 7 int boolean
  · exact variant_merge 7 int boolean

theorem eq_sound {e : Equation} (ok : eqOK e = true) : Holds model e := by
  rcases GeneralDeclarativeWitnessProblem349.splitOr ok with known|rest
  · exact rigid_sound (of_decide_eq_true known)
  · cases e with
    | mk name body =>
      change decide (80 ≤ name ∧ body = payload) = true at rest
      obtain ⟨large,rfl⟩ := of_decide_eq_true rest
      have not7 : name ≠ 7 := by omega
      have not8 : name ≠ 8 := by omega
      have lemma : (model name).1 = entire := by simp [model,kind,ty,not7,not8,large]
      change Equivalent (model name).1 entire
      rw [lemma]
      exact eqv_refl _

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) && s.equations.all eqOK

theorem current_checked : (data.map (fun q => covers q.state)).getD false = true := by decide +kernel

theorem model_fits {d : Data} (found : data = some d) : Models d.state model := by
  have attested := current_checked
  rw [found] at attested
  have ⟨normal,rows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers d.state = true from attested)
  have ⟨plain,ranges⟩ := GeneralDeclarativeWitnessProblem349.splitAnd normal
  have none := List.isEmpty_iff.mp ranges
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro e ext
    exact atom_sound e (List.all_eq_true.mp plain e ext)
  · intro edge ext
    rw [none] at ext
    cases ext
  · intro e ext
    exact eq_sound (List.all_eq_true.mp rows e ext)

theorem nested_branches_share_actual_model :
    ∃ (d : Data) (root : Node d.state) (a : Accepted root d.environment packet),
      data = some d ∧ Models d.state model ∧
      packet.answer.result = .selected (dictionary a.proof) ∧
      (∀ entry ∈ exactLedger,Meaning model entry) ∧
      ∃ v : Valuation,Evident d.state model v root.input.demand (dictionary a.proof) := by
  have checked := full_preorder_ledger_is_real
  unfold test at checked
  cases got : data with
  | none => rw [got] at checked; cases checked
  | some d =>
    cases selected : checkedRoot d with
    | none => simp [got,selected] at checked
    | some root =>
      cases output : read root d.environment authors d.ordered packet with
      | none =>
        have only : (read root d.environment authors d.ordered
            {packet with outputs := id exactLedger}).isSome = true := by
          simpa only [got, Option.map_some, Option.getD_some, selected] using checked
        have only' : (read root d.environment authors d.ordered packet).isSome = true := by
          exact only
        rw [output] at only'
        cases only'
      | some a =>
        have fit := model_fits got
        have full := returned_sound a model fit
        exact ⟨d,root,a,rfl,fit,full.2.1,full.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessMixedNestedModel356
