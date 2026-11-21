import Yulang.GeneralDeclarativeOpaqueNames328
import Yulang.GeneralDeclarativeCovariantIntervals321
import Yulang.GeneralDeclarativeProjectedFrame326
import Yulang.GeneralDeclarativeGrowth327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueIntervals328
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueNames328 (kept first second row expose spelling conservative)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeEntailment320 (Entails model_append literal)
open GeneralDeclarativeCaptureClosure320 (atoms withOrdinary)
open GeneralDeclarativeCovariantIntervals321 (PairBounds record_pair_bounds recorded_components)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeGrowth327 (facts ordinary trans derives fits)
open GeneralDeclarativePairProbe326 (normalized_center)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarationPatterns (normalize)

structure Ends where
  firstLo : Nat
  firstHi : Nat
  secondLo : Nat
  secondHi : Nat

def protect (extra : List Nat) (e : Ends) :=
  [e.firstLo,e.firstHi,e.secondLo,e.secondHi] ++ extra

def low (e : Ends) : Expr := pair (.variable e.firstLo) (.variable e.secondLo)
def high (e : Ends) : Expr := pair (.variable e.firstHi) (.variable e.secondHi)

def left (s : State) (root : Nat) (extra : List Nat) (e : Ends) : Capture :=
  ⟨e.firstLo,first s root (protect extra e),e.firstHi⟩

def right (s : State) (root : Nat) (extra : List Nat) (e : Ends) : Capture :=
  ⟨e.secondLo,second s root (protect extra e),e.secondHi⟩

def ready (s : State) (root : Nat) (extra : List Nat) (e : Ends) : State :=
  withOrdinary (expose s root (protect extra e)) (atoms (left s root extra e) ++ atoms (right s root extra e))

theorem from_old {s : State} (bounds : Bounds s arg) (lo : Entails s ⟨arg.lower,low e⟩)
    (hi : Entails s ⟨arg.upper,high e⟩) (extra : List Nat) :
    PairBounds (expose s arg.center (protect extra e)) arg (left s arg.center extra e) (right s arg.center extra e) := by
  refine ⟨bounds,fun m valid => lo m ((model_append m).mp valid).1,?_,
    fun m valid => hi m ((model_append m).mp valid).1⟩
  exact literal (List.mem_append_right _ List.mem_cons_self)

theorem preserved {s : State} (bounds : Bounds s arg) (lo : Entails s ⟨arg.lower,low e⟩)
    (hi : Entails s ⟨arg.upper,high e⟩) (extra : List Nat) (m) :
    Models s m ↔ ∃ next, Models (ready s arg.center extra e) next ∧
      ∀ n ∈ kept s arg.center (protect extra e), next n = m n := by
  apply (conservative bounds lo hi (protect extra e) m).trans
  exact exists_congr fun next => and_congr_left'
    (record_pair_bounds (from_old bounds lo hi extra) next).symm

theorem bounds {s : State} (root : Nat) (extra : List Nat) (e : Ends) :
    Bounds (ready s root extra e) (left s root extra e) ∧
    Bounds (ready s root extra e) (right s root extra e) :=
  recorded_components (expose s root (protect extra e)) (left s root extra e) (right s root extra e)

theorem actual {s : State} (root : Nat) (extra : List Nat) (e : Ends) :
    Derives (ready s root extra e) (.variable root)
      (pair (.variable (left s root extra e).center) (.variable (right s root extra e).center)) :=
  derives (ordinary _ _) (spelling s root (protect extra e))

theorem compiled {s : State} (arg : Capture) (extra : List Nat) (e : Ends)
    (printed : translate c i (normalize p) = some (pair (.variable l) (.variable r)))
    (usesLeft : cap l = left s arg.center extra e) (usesRight : cap r = right s arg.center extra e) :
    Result (ready s arg.center extra e) (fact c i cap arg p) := by
  refine normalized_center printed (actual arg.center extra e) .capture .capture ?_
  intro o used
  rcases List.mem_cons.mp used with rfl|rest
  · rw [GeneralDeclarativeHead320.byMode,usesLeft]
    exact .refl _
  · cases List.mem_singleton.mp rest
    rw [GeneralDeclarativeHead320.byMode,usesRight]
    exact .refl _

end Yulang.GeneralDeclarativeOpaqueIntervals328
