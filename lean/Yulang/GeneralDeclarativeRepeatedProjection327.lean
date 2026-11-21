import Yulang.GeneralDeclarativeProjectInterval326
import Yulang.GeneralDeclarativeAggregate324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedProjection327
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativePairNames326 (Span appended generated first second keepNames)
open GeneralDeclarativePairSpan326 (state)
open GeneralDeclarativeProjectInterval326 (projectAll names_and_actual unchanged_models pieces)
open GeneralDeclarativePairUnion326 (center_rule)
open GeneralDeclarativeProjectPair326 (recorded)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeMergeCenters324 (Linked)
open GeneralDeclarativeAggregate324 (ready span kept aggregates aligned ready_iff assembled)
open GeneralDeclarativeCaptureClosure320 (ordinary_models)
open GeneralDeclarativeEntailment320 (Entails model_append)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open GeneralDeclarativeRepeatedActual323 (eqAt pair_exact)
open CommonNominalFullCarrier (Equivalent)

def mergeState (s : State) (protect : List Nat) (a b : Span) : State :=
  ready (state s protect a b) (stateNames s ++ keepNames s protect a b)
    (first s protect a b) [second s protect a b]

def merged (s : State) (protect : List Nat) (a b : Span) : Capture :=
  span (state s protect a b) (stateNames s ++ keepNames s protect a b)
    (first s protect a b) [second s protect a b]

/-- A read of the original center as containing two occurrences of the
same source expression forces agreement of the two independently
projected actual terms. Lower/upper values play no part in this step. -/
theorem same_from_actual_source {s : State} {arg : Capture}
    (midSeen : Derives s (.variable arg.center) mid)
    (read : projectAll low mid high = some (l,r))
    (sameSource : Derives s (.variable arg.center) (pair shared shared))
    (m) (valid : Models s m) : eqAt m l.actual r.actual := by
  have heard := center_rule midSeen (recorded (pieces read).2.1) m valid
  have same := semantic sameSource m valid
  have pairSame := (pair_exact ..).mp (eqv_trans (eqv_symm heard) same)
  exact eqv_trans pairSame.1 (eqv_symm pairSame.2)

theorem link_from_observations {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (protect : List Nat)
    (sameSource : Derives s (.variable arg.center) (pair shared shared)) :
    Linked (state s protect l r) (first s protect l r) [second s protect l r] := by
  intro m valid entry inside
  rcases List.mem_cons.mp inside with rfl|remaining
  · exact eqv_refl _
  cases List.mem_singleton.mp remaining
  have ordinary := (unchanged_models bounds lowSeen midSeen highSeen read protect m).mp valid
  have old := ((model_append m).mp ordinary).1
  have equates := same_from_actual_source midSeen read sameSource m old
  have lDef := semantic (generated s protect l r).1.2.1 m ordinary
  have rDef := semantic (generated s protect l r).2.2.1 m ordinary
  exact eqv_trans rDef (eqv_trans (eqv_symm equates) (eqv_symm lDef))

/-- Name two projected nonpoint spans, then merge them using the
approved lower union and upper intersection. Existing names and the
chosen actual source center are not replaced by either endpoint. -/
theorem merge_from_source {s : State} {arg : Capture}
    (bounds : Bounds s arg) (lowSeen : Derives s (.variable arg.lower) low)
    (midSeen : Derives s (.variable arg.center) mid) (highSeen : Derives s (.variable arg.upper) high)
    (read : projectAll low mid high = some (l,r)) (protect : List Nat)
    (sameSource : Derives s (.variable arg.center) (pair shared shared)) :
    Bounds (mergeState s protect l r) (merged s protect l r) ∧
    (∀ m, Models s m → ∃ next, Models (mergeState s protect l r) next ∧
      ∀ n ∈ stateNames s ++ keepNames s protect l r, next n = m n) := by
  obtain ⟨lBound,rBound,projection,_⟩ := names_and_actual bounds lowSeen midSeen highSeen read protect
  let orig := stateNames s ++ keepNames s protect l r
  have each : ∀ a ∈ first s protect l r :: [second s protect l r], Bounds (state s protect l r) a := by
    intro a m
    rcases List.mem_cons.mp m with rfl|h
    · exact lBound
    cases List.mem_singleton.mp h
    exact rBound
  refine ⟨GeneralDeclarativeAggregate324.now_bounds _ _ _ _,?_⟩
  intro m valid
  obtain ⟨intermediate,present,holds⟩ := (projection m).mp valid
  obtain ⟨next,existsHere,retained⟩ := GeneralDeclarativeAggregate324.aggregate_model (extra := orig) each
    (link_from_observations bounds lowSeen midSeen highSeen read protect sameSource) intermediate present
  exact ⟨next,existsHere,fun n seen => (retained n
    (List.mem_append_right _ (List.mem_append_left _ seen))).trans (holds n seen)⟩

end Yulang.GeneralDeclarativeRepeatedProjection327
