import Yulang.GeneralDeclarativeWitnessMixedReleaseFixture352
import Yulang.GeneralDeclarativeTaggedFixtureModel340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralDeclarativeWitnessMixedReleaseModel352
open GeneralDeclarativeWitnessMixedFixture352 (author answer parentProjectionRows)
open GeneralDeclarativeWitnessMixedReleaseFixture352 (solution problem key stamp projectionRows released_named_arm)
open GeneralDeclarativeWitnessWriterFixture351 (sourceEq)
open GeneralDeclarativeWitnessMixedRelease352 (Wire Accepted checked two_reports)

open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeTaggedFixture340 (whole)
open GeneralDeclarativeTaggedFixtureModel340 (int boolean actualRoot entire)
open GeneralDeclarativeWitnessOrderedFixture350 (root rootOutput)
open GeneralDeclarativeWitnessRecordFixture349 (center)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonNominalFullCarrier (Ty variant record exactEmpty emptyRecord subtype_refl
  exactEmpty_below_width common_record_mono Subtype)

inductive Kind where
  | outerExact | outerOpen | firstTag | lastTag | mergedTag | endExact | endOpen | whole | exactWriter | bindInt
  deriving DecidableEq

def ty : Kind → Ty
  | .outerExact => record 7 actualRoot exactEmpty
  | .outerOpen => record 7 actualRoot emptyRecord
  | .firstTag => variant 7 int
  | .lastTag => variant 7 boolean
  | .mergedTag => actualRoot
  | .endExact => exactEmpty
  | .endOpen => emptyRecord
  | .whole => entire
  | .exactWriter => record 8 int exactEmpty
  | .bindInt => int

def category (n : Nat) : Kind :=
  if n ∈ [0,1] then .outerExact else if n = 2 then .outerOpen
  else if n = 8 then .firstTag else if n = 9 then .lastTag
  else if n = 10 then .exactWriter else if n ∈ [100,101,102,106,107] then .bindInt
  else if n ∈ [23,24,28,103,104,105,108,109] then .endExact else if n ∈ [25,29] then .endOpen
  else if 50 ≤ n then .whole else .mergedTag

def model : Assignment := fun n => (ty (category n),Common.rowEmpty)

def allows (l h : Kind) : Bool :=
  decide (l = h ∨ (l = .endExact ∧ h = .endOpen) ∨ (l = .outerExact ∧ h = .outerOpen))

theorem allowed {l h : Kind} (okay : allows l h = true) : Subtype (ty l) (ty h) := by
  rcases of_decide_eq_true okay with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact subtype_refl _
  · exact exactEmpty_below_width
  · exact common_record_mono 7 (subtype_refl _) exactEmpty_below_width

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var h) => allows (category l) (category h)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (h : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l r =>
    cases l <;> cases r <;> try cases h
    exact allowed h
  | rowLe _ _ => cases h

def rigid : List Equation := author ++ [center,rootOutput,sourceEq] ++ parentProjectionRows ++ projectionRows

local instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (GeneralDeclarativeWitnessLiteral349.eqExpr a b = true)
    (GeneralDeclarativeWitnessLiteral349.eq_expr a b)

def eqOK (e : Equation) : Bool :=
  decide (e ∈ rigid) ||
    (match e.right with
    | .variant 7 (.variable n) => decide (e.left = 21 ∧ (50 ≤ n ∧ n < 100))
    | _ => decide ((50 ≤ e.left ∧ e.left < 100) ∧ e.right = whole))

theorem eq_rigid {e : Equation} (h : e ∈ rigid) : Holds model e := by
  simp only [rigid,author,parentProjectionRows,projectionRows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with (((rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl))|(rfl|rfl|rfl|rfl|rfl|rfl))|(rfl|rfl|rfl|rfl|rfl|rfl) <;> exact eqv_refl _

theorem tails (n : Nat) (large : 50 ≤ n ∧ n < 100) : (model n).1 = entire := by
  have limits : n ∉ [0,1] ∧ n ≠ 2 ∧ n ≠ 8 ∧ n ≠ 9 ∧ n ≠ 10 ∧ n ∉ [100,101,102,106,107] ∧
      n ∉ [23,24,28,103,104,105,108,109] ∧ n ∉ [25,29] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega
  obtain ⟨h0,h2,h8,h9,h10,hw,he,ho⟩ := limits
  simp [model,category,h0,h2,h8,h9,h10,hw,he,ho,large.1,ty]

theorem eq_sound {e : Equation} (certified : eqOK e = true) : Holds model e := by
  rcases GeneralDeclarativeWitnessProblem349.splitOr certified with yes|other
  · exact eq_rigid (of_decide_eq_true yes)
  · rcases e with ⟨lhs,rhs⟩
    dsimp only at other
    split at other
    · rename_i n
      obtain ⟨rfl,large⟩ := of_decide_eq_true other
      change CommonNominalFullCarrier.Equivalent actualRoot (variant 7 (model n).1)
      rw [tails n large]
      exact variant_merge 7 int boolean
    · obtain ⟨large,rfl⟩ := of_decide_eq_true other
      change CommonNominalFullCarrier.Equivalent (model lhs).1 entire
      rw [tails lhs large]
      exact eqv_refl _

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && decide (s.normal.intervals = [(0,1),(1,2)])) &&
  s.equations.all eqOK

theorem actual_covered :
    (solution.map (fun (s,_) => covers s)).getD false = true := by decide +kernel

theorem same_model {s : State} {code : Wire} (constructed : solution = some (s,code)) : Models s model := by
  have seen := actual_covered
  rw [constructed] at seen
  have ⟨ordinaryEq,eqs⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers s = true from seen)
  have ⟨ordinary,checkedIntervals⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ordinaryEq
  have actualIntervals : s.normal.intervals = [(0,1),(1,2)] := of_decide_eq_true checkedIntervals
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a h
    exact atom_sound a (List.all_eq_true.mp ordinary a h)
  · intro pair h
    rw [actualIntervals] at h
    rcases List.mem_cons.mp h with rfl|somePair
    · exact subtype_refl _
    · cases List.mem_singleton.mp somePair
      exact common_record_mono 7 (subtype_refl _) exactEmpty_below_width
  · intro e h
    exact eq_sound (List.all_eq_true.mp eqs e h)

theorem nonvacuous :
    ∃ (s : State) (wire : Wire) (a : Accepted (problem s [key]) [stamp] wire answer),
      solution = some (s,wire) ∧ Models s model ∧
      (∃ writer, wire.priorReport.result = .selected writer ∧
        Evidence (registry a.prior.producer.global.table)
          (interpretation a.prior.producer.global.table.snapshot) model
          GeneralDeclarativeWitnessMixedReleaseFixture352.producerDemand writer) ∧
      Evidence (registry a.consumer.global.table) (interpretation a.consumer.global.table.snapshot) model root
        (.node 92 [.node 93 [],.node 94 []]) := by
  have result := released_named_arm
  unfold GeneralDeclarativeWitnessMixedReleaseFixture352.test at result
  cases got : solution with
  | none => simp [got] at result
  | some pair =>
    obtain ⟨s,wire⟩ := pair
    have h : GeneralDeclarativeWitnessMixedRelease352.check (problem s [key]) [stamp] wire answer = true := by
      simpa [got] using result
    obtain ⟨a⟩ := checked h
    have fit := same_model got
    obtain ⟨writer,printed,_,both⟩ :=
      two_reports a (.node 92 [.node 93 [],.node 94 []]) rfl
    have proof := both model fit
    exact ⟨s,wire,a,rfl,fit,⟨writer,printed,proof.1⟩,proof.2.1⟩

end Yulang.GeneralDeclarativeWitnessMixedReleaseModel352
