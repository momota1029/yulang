import Yulang.GeneralStoppedDisplayProjection335
import Yulang.GeneralDeclarativeWitnessClassify334
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralStoppedDisplayGuard335
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (display wrap constructors roles)
open GeneralStoppedDisplayProjection335
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction backed_iff)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl Ready knows_row alias_mono)
open GeneralDeclarativePriority321 (Candidates Recurs Survives)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeEndpointProbe321 (HeadMatches Matches)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Declaration)
open GeneralNominalCenteredHeadWFSource (Coverage ConstructorUse)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)

theorem original_rows {e : Equation} (inside : e ∈ (restriction (supported done)).equations) :
    e ∈ ordinary.equations :=
  (supported done).ordinary ((backed_iff (supported done) e).mp inside).choose_spec.1

def acceptable (a : PresenceNormalForm.Atom Nat) : Bool :=
  match a with
  | .tyLe (.var x) (.var y) => decide (x = y)
  | _ => true

theorem diagonal_intervals : ordinary.normal.intervals.all (fun x => decide (x.1 = x.2)) = true := by
  rfl

theorem diagonal_atoms : ordinary.normal.ordinary.all acceptable = true := by
  decide +kernel

theorem bounds_identity (b : Bound ordinary.normal x y) : x = y := by
  induction b with
  | refl => rfl
  | trans _ _ a b => exact a.trans b
  | interval given => exact of_decide_eq_true (List.all_eq_true.mp diagonal_intervals _ given)
  | constraint given => exact of_decide_eq_true (List.all_eq_true.mp diagonal_atoms _ given)

theorem alias_identity (link : Alias ordinary x y) : x = y := by
  induction link with
  | bounds a _ => exact bounds_identity a
  | forward row | backward row =>
    rcases List.mem_cons.mp row with first|second
    · cases first
    · have impossible := List.mem_singleton.mp second
      cases impossible
  | trans _ _ a b => exact a.trans b

theorem supported_alias_identity (link : Alias (restriction (supported done)) x y) : x = y :=
  alias_identity (alias_mono (s := restriction (supported done)) (t := ordinary) rfl (fun _ h => original_rows h) link)

theorem no_cycles : ∀ n, ¬AliasCycle ordinary (observed ordinary) n := by
  apply graph_no_cycle (fun n => if n = 0 then 1 else 0) (fun _ _ h => congrArg (fun n : Nat => if n = 0 then (1 : Nat) else 0) (alias_identity h))
  rintro n tag child ⟨e,there,compute⟩ member
  rcases List.mem_cons.mp there with known|rest
  · cases known
    cases compute
    cases List.mem_singleton.mp member
    decide +kernel
  · cases List.mem_singleton.mp rest
    cases compute
    cases member

def waiting (_ : Demand) (_ : Declaration) : Prop := False

theorem safe (tests : Candidates) (d : Demand) : ¬Recurs ordinary registry interpretation tests d := by
  rintro (⟨a,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,_,source,_,cycle⟩)
  · exact no_cycles a.lower cycle
  · exact no_cycles source cycle

abbrev listCode : Expr := .nominal 0 [.variable 0]
abbrev intCode : Expr := .primitive (.scalar .int) []

theorem list_print : translate constructors interpretation (normalize (.app 0 [.var 0])) = some listCode := rfl
theorem int_print : translate constructors interpretation (normalize (.app 2 [])) = some intCode := rfl

theorem list_trace (done : Nat → Prop) (mode) :
    Trace (restriction (supported done)) mode 0 listCode [⟨0,.actual,1⟩] :=
  .nominal (args := [1]) (alias_refl _) (list_allowed done) (.cons .capture .nil)

theorem int_trace (done : Nat → Prop) (mode) :
    Trace (restriction (supported done)) mode 1 intCode [] :=
  .primitive (args := []) (alias_refl _) (int_allowed done) .nil

theorem parent_ready (done : Nat → Prop) : Ready (supported done) parentDemand := by
  intro col present
  cases List.mem_singleton.mp present
  exact ⟨_,knows_row (list_allowed done) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (supported done) childDemand := by
  intro col present
  cases List.mem_singleton.mp present
  exact ⟨_,knows_row (int_allowed done) rfl⟩

theorem parent_matches (done : Nat → Prop) :
    HeadMatches (restriction (supported done)) constructors interpretation parentDemand display :=
  .cons ⟨point_bounded _ _,_,_,_,list_print,list_trace done .lower,list_trace done .upper⟩ .nil

theorem child_matches (done : Nat → Prop) :
    HeadMatches (restriction (supported done)) constructors interpretation childDemand intDisplay :=
  .cons ⟨point_bounded _ _,_,_,_,int_print,int_trace done .lower,int_trace done .upper⟩ .nil

theorem covered : Coverage registry interpretation := by
  have lc : ConstructorUse constructors interpretation 0 1 :=
    ⟨⟨[.type],0⟩,rfl,rfl,.inr ⟨rfl,rfl⟩⟩
  have ic : ConstructorUse constructors interpretation 2 0 :=
    ⟨⟨[],2⟩,rfl,rfl,.inl ⟨.scalar .int,rfl,rfl⟩⟩
  constructor
  · intro d member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact ⟨⟨⟨ic,True.intro⟩,True.intro⟩,fun _ h => False.elim (List.not_mem_nil h),
        fun _ h => False.elim (List.not_mem_nil h)⟩
    · refine ⟨⟨⟨lc,True.intro,True.intro⟩,True.intro⟩,?_,fun _ h => False.elim (List.not_mem_nil h)⟩
      intro c chosen; cases List.mem_singleton.mp chosen
      exact ⟨⟨True.intro,True.intro⟩,fun _ h => False.elim (List.not_mem_nil h)⟩
    · refine ⟨⟨⟨lc,True.intro,True.intro⟩,True.intro⟩,?_,?_⟩
      · intro c chosen; cases List.mem_singleton.mp chosen
        refine ⟨⟨True.intro,True.intro⟩,?_⟩
        intro eq present; cases List.mem_singleton.mp present; trivial
      · intro eq chosen; cases List.mem_singleton.mp chosen
        exact ⟨lc,True.intro,True.intro⟩
  · intro role name body impossible
    change (roles role).assoc name = some (some body) at impossible
    by_cases first : role = 1
    · subst role
      change (if name = 0 then some none else none) = some (some body) at impossible
      split at impossible <;> cases impossible
    by_cases second : role = 2
    · subst role
      change (if name = 1 then some none else none) = some (some body) at impossible
      split at impossible <;> cases impossible
    unfold roles at impossible
    rw [ite_eq_right first,ite_eq_right second] at impossible
    split at impossible <;> cases impossible


theorem parent_declared : Declared registry parentDemand := fun _ h => (List.not_mem_nil h).elim
theorem child_declared : Declared registry childDemand := fun _ h => (List.not_mem_nil h).elim

end Yulang.GeneralStoppedDisplayGuard335
