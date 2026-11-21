import Yulang.GeneralDeclarativeRepeatModels327
import Yulang.GeneralDeclarativeEndpointAlias327
import Yulang.GeneralDeclarativePlacementEquiv327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace Yulang.GeneralDeclarativeAliasAuthority327
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeExampleSource320 (point leaf leaf_checked)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarations (Registry Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Origin Supported restriction backed_iff from_source)
open GeneralDeclarativeLowerKnown321 (Alias Knows Ready Delayed knows_row knows_alias alias_refl)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Graph321 (Descends Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeProjectedFrame326 (Rule Frame sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativePlacementEquiv327 (RequestSame)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Dictionary)
open CommonNominalFullCarrier (Equivalent)

abbrev scalar : Equation := ⟨0,.primitive (.scalar .int) []⟩
abbrev imported : Equation := ⟨1,.variable 0⟩
abbrev fixedA : Equation := ⟨5,.variable 0⟩
abbrev fixedB : Equation := ⟨5,.variable 1⟩
abbrev rows : List Equation := [scalar,imported,fixedA,fixedB]
abbrev state : State := ⟨⟨[],[]⟩,rows⟩
abbrev a : Demand := ⟨2,[point 0],[⟨1,5⟩]⟩
abbrev b : Demand := ⟨2,[point 1],[⟨1,5⟩]⟩
abbrev reg : Registry := ⟨constructors,roles,[leaf]⟩
abbrev interp := GeneralDeclarativeRepeatDecl327.interp

def originates (e : Equation) (o : Origin) : Prop :=
  (e = scalar ∧ o = .source) ∨ (e = imported ∧ o = .output 42) ∨
  (e = fixedA ∧ o = .output 1) ∨ (e = fixedB ∧ o = .output 1)

def support (done : Nat → Prop) : Supported state done := ⟨originates,by
  intro row origin h
  rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> simp [rows]⟩

abbrev emptyDone : Nat → Prop := fun _ => False
abbrev realDone : Nat → Prop := fun n => n = 42

theorem literal (done : Nat → Prop) : scalar ∈ (restriction (support done)).equations :=
  from_source _ (.inl ⟨rfl,rfl⟩)

theorem initial_only {e : Equation} (there : e ∈ (restriction (support emptyDone)).equations) :
    e = scalar := by
  obtain ⟨origin,fromWhere,on⟩ := (backed_iff ..).mp there
  rcases fromWhere with ⟨rfl,_⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
  · rfl
  all_goals cases on with | completed impossible => exact False.elim impossible

theorem alias_restricted {a b : Nat} (later : Alias (restriction (support emptyDone)) a b) :
    a = b := by
  have plain {a b : Nat} (line : Bound (restriction (support emptyDone)).normal a b) : a = b := by
    induction line with
    | refl => rfl
    | interval no => cases no
    | constraint no => cases no
    | trans _ _ x y => exact x.trans y
  induction later with
  | bounds a _ => exact plain a
  | forward used => have no := congrArg Equation.right (initial_only used); cases no
  | backward used => have no := congrArg Equation.right (initial_only used); cases no
  | trans _ _ first last => exact first.trans last

theorem authorized_before : Ready (support emptyDone) a := by
  intro q used
  cases List.mem_singleton.mp used
  exact ⟨_,knows_row (literal _) rfl⟩

theorem not_before : Delayed (support emptyDone) b := by
  refine ⟨point 1,List.mem_cons_self,?_⟩
  rintro tag ⟨row,stored,linked,_⟩
  cases initial_only stored
  have no := alias_restricted linked
  cases no

theorem authorized_later : Ready (support realDone) b := by
  intro q used
  cases List.mem_singleton.mp used
  have covered : imported ∈ (restriction (support realDone)).equations :=
    (backed_iff ..).mpr ⟨.output 42,.inr (.inl ⟨rfl,rfl⟩),.completed rfl⟩
  exact ⟨_,knows_alias (.forward covered) (knows_row (literal _) rfl)⟩

theorem equal_in_every_model (m) (valid : Models state m) : RequestSame m a b := by
  have eq : Equivalent (m 1).1 (m 0).1 := valid.2 imported (by simp [rows])
  have swap := GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm eq
  exact ⟨rfl,.cons ⟨swap,swap,swap⟩ .nil,rfl⟩

theorem fits : Models state (fun _ => (.base .int,Common.rowEmpty)) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ bad => False.elim (List.not_mem_nil bad)⟩,?_⟩
  intro row inState
  change row ∈ rows at inState
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at inState
  rcases inState with rfl|rfl|rfl|rfl <;> exact eqv_refl _

end Yulang.GeneralDeclarativeAliasAuthority327
