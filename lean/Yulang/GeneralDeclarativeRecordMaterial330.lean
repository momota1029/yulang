import Yulang.GeneralDeclarativeRecordSpine330
import Yulang.GeneralDeclarativeOpaqueConserve328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordMaterial330
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeRecordSpine330 (Spine exact_subtraction)
open GeneralDeclarativeRecordResidual323 (withTail prefix_congr)
open GeneralDeclarativeEntailment320 (Entails appendFacts model_append literal conservative_append)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeGrowth327 (facts trans)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeNewNames321 (supply after old_plus_extra)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleCanonicalRows (Row normalize residual)

def tailExpr (raw : Row Expr) (keys : List Nat) (terminal : Expr) : Expr :=
  withTail (residual keys (normalize raw)) terminal
def tailRow (s : State) (root : Nat) (protect : List Nat) (raw : Row Expr)
    (keys : List Nat) (terminal : Expr) : Equation :=
  let rhs := tailExpr raw keys terminal
  ⟨after ((stateNames s ++ root :: protect) ++ ([rhs].flatMap names)),rhs⟩
def namedTail (s : State) (root : Nat) (protect : List Nat) (raw : Row Expr)
    (keys : List Nat) (terminal : Expr) : State :=
  appendFacts s [tailRow s root protect raw keys terminal]
def readingRow (s : State) (root : Nat) (protect : List Nat) (raw picked : Row Expr)
    (keys : List Nat) (terminal : Expr) : Equation :=
  ⟨root,withTail picked (.variable (tailRow s root protect raw keys terminal).left)⟩
def ready (s : State) (root : Nat) (protect : List Nat) (raw picked : Row Expr)
    (keys : List Nat) (terminal : Expr) : State :=
  appendFacts (namedTail s root protect raw keys terminal)
    [readingRow s root protect raw picked keys terminal]

theorem right {s : State} {p : Supported s done}
    (observed : Spine (restriction p) root raw terminal) (unique : keys.Nodup)
    (printed : order (normalize raw) keys = some picked) (protect : List Nat) :
    Entails (namedTail s root protect raw keys terminal) (readingRow s root protect raw picked keys terminal) := by
  let t := namedTail s root protect raw keys terminal
  let row := tailRow s root protect raw keys terminal
  intro m valid
  have old := (model_append (rows := [row]) (s := s) m).mp valid
  have whole := exact_subtraction observed unique printed m old.1
  have chosen := (literal (s := t) (row := row) (List.mem_append_right _ List.mem_cons_self)) m valid
  exact eqv_trans whole (prefix_congr m picked (eqv_symm chosen))

/-- Source-driven subtraction defines the *actual* residual logical
name, not an arbitrary existential tail in a full record equation.
Both additions are conservative over old names and fixed targets. -/
theorem preserved {s : State} {p : Supported s done}
    (observed : Spine (restriction p) root raw terminal) (unique : keys.Nodup)
    (printed : order (normalize raw) keys = some picked) (protect : List Nat) :
    Retains s (ready s root protect raw picked keys terminal) protect := by
  let row := tailRow s root protect raw keys terminal
  let t := namedTail s root protect raw keys terminal
  let read := readingRow s root protect raw picked keys terminal
  have stored : supply s (root :: protect) [tailExpr raw keys terminal] = [row] := rfl
  refine ⟨trans (facts _ _) (facts _ _),?_⟩
  intro m valid
  obtain ⟨lift,kept⟩ := old_plus_extra s (root::protect) [tailExpr raw keys terminal] m valid
  rw [stored] at lift kept
  have entailed := right observed unique printed protect
  refine ⟨_,(conservative_append (s := t) (rows := [read]) (fun e found => ?_) _).mpr lift,?_⟩
  · cases List.mem_singleton.mp found
    exact entailed
  · intro n seen
    rcases List.mem_append.mp seen with old|explicit
    · exact kept n (List.mem_append_left _ old)
    · exact kept n (List.mem_append_right _ (List.mem_cons_of_mem _ explicit))

theorem read_ordinary {s : State} (root : Nat) (protect : List Nat) (raw picked : Row Expr)
    (keys : List Nat) (terminal : Expr) :
    Derives (ready s root protect raw picked keys terminal) (.variable root)
      (withTail picked (.variable (tailRow s root protect raw keys terminal).left)) :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem read_tail {s : State} (root : Nat) (protect : List Nat) (raw picked : Row Expr)
    (keys : List Nat) (terminal : Expr) :
    Derives (ready s root protect raw picked keys terminal)
      (.variable (tailRow s root protect raw keys terminal).left) (tailExpr raw keys terminal) :=
  .row (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))

end Yulang.GeneralDeclarativeRecordMaterial330
