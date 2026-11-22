import Yulang.GeneralDeclarativeWitnessCovariantIntervalNested353
import Yulang.GeneralDeclarativeWitnessCovariantJoin353
import Yulang.GeneralDeclarativeTaggedFixtureModel340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 31000000
namespace Yulang.GeneralDeclarativeWitnessCovariantIntervalNestedModel353
open GeneralDeclarativeWitnessCovariantIntervalNested353 (rootProblem ordinaryRows data report check success environment)
open GeneralDeclarativeWitnessCovariantIntervalForest353 (Wire Accepted decode semantic)
open GeneralDeclarativeWitnessCovariantIntervalFixture353 (upperEq)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open GeneralDeclarativeWitnessCovariantOrigin353 (ModelsAt Valuation assigned)
open GeneralDeclarativeWitnessCovariantFixture353 (out)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeTaggedFixture340 (whole)
open GeneralDeclarativeTaggedFixtureModel340 (int boolean entire actualRoot)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (All₂)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_refl variant)

inductive Kind where
  | first | last | tagged | scalar | wider
  deriving DecidableEq

def kind (n : Nat) : Kind :=
  if n = 7 then .first else if n = 8 then .last else if n = 10 then .wider else if 50 ≤ n then .scalar else .tagged

def ty : Kind → Ty
  | .first => variant 7 int
  | .last => variant 7 boolean
  | .tagged => actualRoot
  | .scalar => entire
  | .wider => .union actualRoot (.base .unit)

def model : Assignment := fun n => (ty (kind n),Common.rowEmpty)

def allowed (a b : Kind) : Bool :=
  decide (a = b ∨ (a = .first ∧ b = .tagged) ∨ (a = .tagged ∧ b = .wider))

theorem allowed_model {a b : Kind} (yes : allowed a b = true) : Subtype (ty a) (ty b) := by
  rcases of_decide_eq_true yes with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact subtype_refl _
  · exact ((CommonNominalFullCarrier.common_union_is_join (variant 7 int) (variant 7 boolean) actualRoot).mp
      (subtype_refl _)).1
  · exact ((CommonNominalFullCarrier.common_union_is_join actualRoot (.base .unit) (.union actualRoot (.base .unit))).mp
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

def rigid : List Equation := ordinaryRows ++ out
local instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (GeneralDeclarativeWitnessLiteral349.eqExpr a b = true)
    (GeneralDeclarativeWitnessLiteral349.eq_expr a b)

def eqOK (e : Equation) : Bool :=
  decide (e ∈ rigid) ||
    (match e.right with
    | .variant 7 (.variable n) => decide (e.left = 9 ∧ 50 ≤ n)
    | _ => decide (50 ≤ e.left ∧ e.right = whole))

theorem rigid_model {e : Equation} (h : e ∈ rigid) : Holds model e := by
  simp only [rigid,ordinaryRows,out,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> exact eqv_refl _

theorem tail_kind (n : Nat) (large : 50 ≤ n) : (model n).1 = entire := by
  have first : n ≠ 7 := by omega
  have last : n ≠ 8 := by omega
  have n10 : n ≠ 10 := by omega
  simp [model,kind,ty,first,last,n10,large]

theorem eq_sound {e : Equation} (valid : eqOK e = true) : Holds model e := by
  rcases GeneralDeclarativeWitnessProblem349.splitOr valid with original|newRow
  · exact rigid_model (of_decide_eq_true original)
  · cases e with
    | mk l r =>
      dsimp only at newRow
      split at newRow
      · rename_i n
        obtain ⟨rfl,large⟩ := of_decide_eq_true newRow
        change Equivalent actualRoot (variant 7 (model n).1)
        rw [tail_kind n large]
        exact variant_merge 7 int boolean
      · obtain ⟨large,rfl⟩ := of_decide_eq_true newRow
        change Equivalent (model l).1 entire
        rw [tail_kind l large]
        exact eqv_refl _

def covers (s : State) : Bool :=
  (s.normal.ordinary.all atomOK && s.normal.intervals.isEmpty) && s.equations.all eqOK

theorem actual_model_fields : (data.map fun (_,s,_) => covers s).getD false = true := by decide +kernel

theorem model_fits {f : GeneralDeclarativeWitnessCompiler350.Finished} {s : State} {w : Wire}
    (selected : data = some (f,s,w)) : Models s model := by
  have ok := actual_model_fields
  rw [selected] at ok
  obtain ⟨bounds,rows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers s = true from ok)
  have ⟨atoms,intervals⟩ := GeneralDeclarativeWitnessProblem349.splitAnd bounds
  have empty := List.isEmpty_iff.mp intervals
  refine ⟨⟨fun a used => atom_sound a (List.all_eq_true.mp atoms a used),?_⟩,
    fun e used => eq_sound (List.all_eq_true.mp rows e used)⟩
  intro x used
  rw [empty] at used
  cases used

def valuation : Valuation
  | 30 => some ⟨13,0,(assigned model 7).1⟩
  | 31 => some ⟨13,0,(assigned model 8).1⟩
  | 20 => some ⟨13,0,(assigned model 9).1⟩
  | 11 => some ⟨13,0,(assigned model 7).1⟩
  | 21 => some ⟨13,0,(assigned model 10).1⟩
  | _ => none

theorem typed_rows : ∀ q ∈ rootProblem.rows, GeneralDeclarativeWitnessCovariantOrigin353.HasView model valuation q := by
  intro q seen
  change q ∈ (GeneralDeclarativeWitnessCovariantIntervalFixture353.problem).rows at seen
  simp only [GeneralDeclarativeWitnessCovariantIntervalFixture353.problem,GeneralDeclarativeWitnessCovariantFixture353.rows,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl|rfl|rfl <;> exact ⟨_,rfl,rfl,rfl,Common.equivalent_refl _⟩

theorem exact_nonpoint_forest :
    ∃ (f : GeneralDeclarativeWitnessCompiler350.Finished) (s : State) (w : Wire)
      (a : Accepted rootProblem (environment f) s w report),
        data = some (f,s,w) ∧ Models s model ∧
        (∃ l c h : GeneralDeclarativeWitnessCovariantOrigin353.View,
          valuation a.root.facts.arg.lower = some l ∧ valuation a.root.facts.arg.center = some c ∧
          valuation a.root.facts.arg.upper = some h ∧
          DeclaredSubtype (table w.interval.center.box) (View.head l) (View.head c) ∧
          DeclaredSubtype (table w.interval.center.box) (View.head c) (View.head h)) ∧
        All₂ (Evidence (registry a.ordinary) (interpretation a.ordinary.snapshot) model)
          a.root.compiler.compiled.kids [.node 93 [],.node 94 []] ∧
        w.rootOut.outputRows.map Equation.left = [5,6] ∧
        ∀ e ∈ w.rootOut.outputRows,Holds model e := by
  have done := success
  unfold check at done
  cases z : data with
  | none => simp [z] at done
  | some item =>
    obtain ⟨f,s,w⟩ := item
    have accepted : (decode rootProblem (environment f) s w report).isSome = true := by simpa [z] using done
    cases found : decode rootProblem (environment f) s w report with
    | none => simp [found] at accepted
    | some a =>
      have fit := model_fits z
      have verified := semantic a model valuation fit typed_rows
      have dict := verified.2.2.2.1
      change CommonRoleOutermostResolver.Result.selected (.node 92 [.node 93 [],.node 94 []]) =
        .selected (.node a.root.facts.center.decl.id a.children.entries) at dict
      have entries := (CommonRoleOutermostResolver.Dictionary.node.inj
        (CommonRoleOutermostResolver.Result.selected.inj dict)).2.symm
      have kids := verified.2.2.1
      rw [entries] at kids
      exact ⟨f,s,w,a,rfl,fit,verified.1,kids,verified.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantIntervalNestedModel353
