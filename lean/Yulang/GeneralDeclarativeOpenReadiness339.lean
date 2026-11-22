import Yulang.GeneralDeclarativeCompoundOpenFixture338
import Yulang.GeneralDeclarativeCompoundFixtureSelection338

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace Yulang.GeneralDeclarativeOpenReadiness339
open GeneralDeclarativeCompoundOpenFixture338
open GeneralDeclarativeRecordDecl326 (registry decl checked)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeLowerKnown321 (Ready Alias alias_refl knows_row)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativePriority321 (Recurs Local)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeCompoundOpenPrefix338 (residuals)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty record exactEmpty Equivalent subtype_refl)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)

abbrev root : Demand := ⟨1,[a],[⟨0,6⟩]⟩
def wait (_ : Demand) (_ : Declaration) : Prop := False
abbrev headCode : Expr := .record 7 (.variable 0) (.variable 1)

theorem named_positive : HeadMatches (restriction p) catalogue interpretation root decl := by
  have lower : GeneralDeclarativeTrace321.Trace (restriction p) .lower 0 headCode
      [⟨0,.lower,3⟩,⟨1,.lower,4⟩] :=
    .record (alias_refl _) (supported List.mem_cons_self) .capture .capture
  have upper : GeneralDeclarativeTrace321.Trace (restriction p) .upper 2 headCode
      [⟨0,.upper,3⟩,⟨1,.upper,4⟩] :=
    .record (alias_refl _) (supported (List.mem_cons_of_mem _ List.mem_cons_self)) .capture .capture
  exact .cons ⟨read_prefix.bound,headCode,_,_,rfl,lower,upper⟩ .nil

def height (n : Nat) := if n < 3 then 1 else 0
def edgeOK (edge : Nat × Nat) : Bool := decide (height edge.1 ≤ height edge.2)
def rowOK (e : Equation) : Bool :=
  match e.right with | .variable n => decide (height e.left = height n) | _ => true
def decreases (e : Equation) : Bool :=
  match shapeOf e.right with
  | none => true
  | some tag => tag.children.all (fun n => decide (height n < height e.left))

theorem rankSafe : ∀ k, ¬AliasCycle s (observed s) k := by
  have edges : s.normal.intervals.all edgeOK = true := by decide +kernel
  have rows : s.equations.all rowOK = true := by decide +kernel
  have shapes : s.equations.all decreases = true := by decide +kernel
  have constraint {a b} (h : Bound s.normal a b) : height a ≤ height b := by
    induction h with
    | interval present => exact of_decide_eq_true (List.all_eq_true.mp edges _ present)
    | constraint absent => cases absent
    | refl _ => exact Nat.le_refl _
    | trans _ _ first last => exact Nat.le_trans first last
  have aliases {x y} (h : Alias s x y) : height x = height y := by
    induction h with
    | bounds first last => exact Nat.le_antisymm (constraint first) (constraint last)
    | forward row => exact of_decide_eq_true (List.all_eq_true.mp rows _ row)
    | backward row => exact (of_decide_eq_true (List.all_eq_true.mp rows _ row)).symm
    | trans _ _ f g => exact f.trans g
  apply graph_no_cycle height (fun _ _ => aliases)
  rintro n tag child ⟨rhs,stored,decoded⟩ member
  have found := List.all_eq_true.mp shapes ⟨n,rhs⟩ stored
  change decreases ⟨n,rhs⟩ = true at found
  unfold decreases at found
  rw [decoded] at found
  exact of_decide_eq_true (List.all_eq_true.mp found child member)

theorem legacy_elected : Elected s registry interpretation p (candidates p registry interpretation wait) root decl := by
  have ready : Ready p root := by
    intro x h; cases List.mem_singleton.mp h
    exact ⟨_,knows_row (supported List.mem_cons_self) rfl⟩
  have safe : ¬Recurs s registry interpretation (candidates p registry interpretation wait) root := by
    rintro (⟨a,_,cy⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cy⟩)
    · exact rankSafe a.lower cy
    · exact rankSafe site cy
  refine ⟨ready,safe,fun ⟨_,_,bad⟩ => bad,⟨⟨List.mem_cons_self,rfl⟩,.inl named_positive⟩,?_⟩
  intro other allowed
  rcases List.mem_cons.mp allowed.1.1 with rfl|later
  · rfl
  · cases List.mem_singleton.mp later
    cases allowed.1.2

def withTail (tail : Ty) : Assignment := fun n =>
  (if n < 3 then record 7 int tail else if n = 4 then tail else int,Common.rowEmpty)

theorem tail_models (tail : Ty) : Models s (withTail tail) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e here
    change e ∈ [(0,1),(1,2)] at here
    rcases List.mem_cons.mp here with equal|last
    · cases equal; exact subtype_refl _
    · cases List.mem_singleton.mp last; exact subtype_refl _
  · intro row here
    change row ∈ [lhs,rhs,scalar] at here
    simp only [List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl <;> exact eqv_refl _

theorem tail_changes :
    ¬ Equivalent (residuals [7] (withTail exactEmpty) a).2.1
      (residuals [7] (withTail (record 8 int exactEmpty)) a).2.1 := by
  change ¬ Equivalent exactEmpty (record 8 int exactEmpty)
  intro same
  have read : GeneralDeclarativeRecordChannel330.project 8 false [] (record 8 int exactEmpty) = some int :=
    GeneralDeclarativeRecordIntervals330.direct 8 false _ _
  obtain ⟨_,impossible⟩ := GeneralDeclarativeRecordPayloads330.has_field read same.1
  cases impossible

/-- Provisional legacy election alone is not evidence that an actual
goal tail is settled. The very same source equations admit two
models with observably different residuals and no supported closure.
This is not a verified selection by the new compiler or a raw solver
counterexample. -/
theorem exact_gap :
    Elected s registry interpretation p (candidates p registry interpretation wait) root decl ∧
    (¬ ∃ r ending, Closed (restriction p) (.variable 4) r ending) ∧
    ∃ m n, Models s m ∧ Models s n ∧
      ¬ Equivalent (residuals [7] m a).2.1 (residuals [7] n a).2.1 :=
  ⟨legacy_elected,by rintro ⟨r,ending,h⟩; exact tail_not_closed h,
   withTail exactEmpty,withTail (record 8 int exactEmpty),tail_models _,tail_models _,tail_changes⟩

end Yulang.GeneralDeclarativeOpenReadiness339
