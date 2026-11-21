import Yulang.GeneralDeclarativePairCenters326
import Yulang.GeneralDeclarativeFreshWhere325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairNames326
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeNewNames321 (after supply old_plus_extra supply_avoids)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

structure Span where
  low : Expr
  actual : Expr
  high : Expr

def terms (a b : Span) : List Expr := [a.low,a.actual,a.high,b.low,b.actual,b.high]

def keepNames (_s : State) (keep : List Nat) (a b : Span) : List Nat :=
  keep ++ (terms a b).flatMap names

def seed (s : State) (keep : List Nat) (a b : Span) : Nat :=
  after ((stateNames s ++ keepNames s keep a b) ++ (terms a b).flatMap names)

def first (s : State) (keep : List Nat) (a b : Span) : Capture :=
  let n := seed s keep a b
  ⟨n,n+1,n+2⟩

def second (s : State) (keep : List Nat) (a b : Span) : Capture :=
  let n := seed s keep a b
  ⟨n+3,n+4,n+5⟩

def appended (s : State) (keep : List Nat) (a b : Span) : State :=
  appendFacts s (supply s (keepNames s keep a b) (terms a b))

def Defines (s : State) (c : Capture) (x : Span) : Prop :=
  Derives s (.variable c.lower) x.low ∧ Derives s (.variable c.center) x.actual ∧
  Derives s (.variable c.upper) x.high

theorem generated (s : State) (keep : List Nat) (a b : Span) :
    Defines (appended s keep a b) (first s keep a b) a ∧
    Defines (appended s keep a b) (second s keep a b) b := by
  refine ⟨⟨.row ?_,.row ?_,.row ?_⟩,⟨.row ?_,.row ?_,.row ?_⟩⟩
  · exact List.mem_append_right _ List.mem_cons_self
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))

/-- Naming the actual projections is a conservative definition even
when they are proper compound expressions. It never alters an old
quantified value or caller-protected fixed output target. -/
theorem projection (s : State) (keep : List Nat) (a b : Span) (m : Assignment) :
    Models s m ↔ ∃ next, Models (appended s keep a b) next ∧
      ∀ n ∈ stateNames s ++ keepNames s keep a b, next n = m n := by
  constructor
  · intro fits
    obtain ⟨model,kept⟩ := old_plus_extra s (keepNames s keep a b) (terms a b) m fits
    exact ⟨_,model,kept⟩
  · rintro ⟨next,valid,kept⟩
    exact (preserves_models s (fun n mentioned => kept n (List.mem_append_left _ mentioned))).mp
      ((model_append next).mp valid).1

end Yulang.GeneralDeclarativePairNames326
