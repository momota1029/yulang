import Yulang.GeneralDeclarativeWitnessTaggedParent352
import Yulang.GeneralDeclarativeTaggedFixtureModel340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralDeclarativeWitnessTaggedParentModel352
open GeneralDeclarativeWitnessTaggedParent352 (root candidate check independently_accepted roots out report)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWitnessMixedForest352 (Problem Code)
open GeneralDeclarativeWitnessMixedWhole352 (Accepted checked selected)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeTaggedFixture340 (whole)
open GeneralDeclarativeTaggedFixtureModel340 (int boolean actualRoot entire)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonNominalFullCarrier (Ty variant Subtype subtype_refl Equivalent)

inductive Kind where
  | outer | armInt | armBool | firstTag | lastTag | mergedTag | whole
  deriving DecidableEq

def ty : Kind → Ty
  | .outer => variant 11 actualRoot
  | .armInt => variant 11 (variant 7 int)
  | .armBool => variant 11 (variant 7 boolean)
  | .firstTag => variant 7 int
  | .lastTag => variant 7 boolean
  | .mergedTag => actualRoot
  | .whole => entire

def category (n : Nat) : Kind :=
  if n = 0 then .outer else if n = 3 then .armInt else if n = 4 then .armBool
  else if n = 8 then .firstTag else if n = 9 then .lastTag else if 50 ≤ n then .whole else .mergedTag

def model : Assignment := fun n => (ty (category n),Common.rowEmpty)

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var h) => decide (category l = category h)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (okay : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l r =>
    cases l <;> cases r <;> try cases okay
    rename_i l r
    have equal : category l = category r := of_decide_eq_true okay
    change Subtype (ty (category l)) (ty (category r))
    rw [equal]
    exact subtype_refl _
  | rowLe _ _ => cases okay

def rawJoin : Expr := .join (.variable 8) (.variable 9)
def rigid : List Equation :=
  roots ++ [out,⟨0,.variant 11 (.variable 26)⟩] ++
  ([20,21,22,23,24,25].map fun n => ⟨n,rawJoin⟩)

local instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (GeneralDeclarativeWitnessLiteral349.eqExpr a b = true)
    (GeneralDeclarativeWitnessLiteral349.eq_expr a b)

def eqOK (e : Equation) : Bool :=
  decide (e ∈ rigid) ||
    (match e.right with
    | .variant 7 (.variable n) => decide (e.left = 26 ∧ 50 ≤ n)
    | _ => decide (50 ≤ e.left ∧ e.right = whole))

theorem eq_rigid {e : Equation} (h : e ∈ rigid) : Holds model e := by
  simp only [rigid,roots,List.mem_append,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with ((rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl))|(rfl|rfl|rfl|rfl|rfl|rfl)
  · exact eqv_symm (variant_merge 11 (variant 7 int) (variant 7 boolean))
  all_goals exact eqv_refl _

theorem tails (n : Nat) (large : 50 ≤ n) : (model n).1 = entire := by
  have neq : n ≠ 0 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 8 ∧ n ≠ 9 := by omega
  obtain ⟨h0,h3,h4,h8,h9⟩ := neq
  simp [model,category,h0,h3,h4,h8,h9,large,ty]

theorem eq_sound {e : Equation} (certified : eqOK e = true) : Holds model e := by
  rcases GeneralDeclarativeWitnessProblem349.splitOr certified with yes|other
  · exact eq_rigid (of_decide_eq_true yes)
  · rcases e with ⟨lhs,rhs⟩
    dsimp only at other
    split at other
    · rename_i n
      obtain ⟨rfl,large⟩ := of_decide_eq_true other
      change Equivalent actualRoot (variant 7 (model n).1)
      rw [tails n large]
      exact variant_merge 7 int boolean
    · obtain ⟨large,rfl⟩ := of_decide_eq_true other
      change Equivalent (model lhs).1 entire
      rw [tails lhs large]
      exact eqv_refl _

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) && s.equations.all eqOK

theorem actual_covered : (candidate.map (fun (p,_) => covers p.current)).getD false = true := by decide +kernel

theorem same_model {p : Problem} {code : Code} (constructed : candidate = some (p,code)) :
    Models p.current model := by
  have seen := actual_covered
  rw [constructed] at seen
  have ⟨ordinaryEq,eqs⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers p.current = true from seen)
  have ⟨ordinary,checkedIntervals⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ordinaryEq
  have noIntervals := List.isEmpty_iff.mp checkedIntervals
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a h
    exact atom_sound a (List.all_eq_true.mp ordinary a h)
  · intro pair h
    rw [noIntervals] at h
    cases h
  · intro e h
    exact eq_sound (List.all_eq_true.mp eqs e h)

theorem nonvacuous :
    ∃ (p : Problem) (code : Code) (a : Accepted p root report),
      candidate = some (p,code) ∧ Models p.current model ∧
      Evidence (registry a.global.table) (interpretation a.global.table.snapshot) model root
        (.node 92 [.node 93 [],.node 94 []]) ∧
      (∀ f ∈ a.diagnostic.fixed, f.equations.map Equation.left =
        f.demand.outputs.map GeneralSourceState.Output.target ∧ ∀ e ∈ f.equations,Holds model e) := by
  have result := independently_accepted
  unfold check at result
  cases got : candidate with
  | none => simp [got] at result
  | some pair =>
    obtain ⟨p,code⟩ := pair
    have h : GeneralDeclarativeWitnessMixedWhole352.check p root code report = true := by
      simpa [got] using result
    obtain ⟨a⟩ := checked h
    have fit := same_model got
    exact ⟨p,code,a,rfl,fit,selected a rfl model fit⟩

end Yulang.GeneralDeclarativeWitnessTaggedParentModel352
