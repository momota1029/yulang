import Yulang.GeneralWhereVersionRootReport317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 49000000
/-! Re-reading the same observed declaration with equal erased inputs
does not allocate another endpoint version. Constructor and provenance
maps (not model values or transient Fin slot positions) control the key. -/
namespace Yulang.GeneralWhereVersionRecompile317
open GeneralNominalCenteredHeadMatPlanData (Same occurrence)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralNominalVersionedFrame231 (capture binder frame)
open GeneralDeferredLadderTransport302 (capture_eq binder_eq frame_eq)
open GeneralVersionedEndpointAddress315 (Side key atCell footprint)
open GeneralWhereVersionCompiler317 (args allocation emissions children schema)
open GeneralNominalCenters
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem variable_eq {p q : Plan roles} (same : Same p q) (mode name) :
    variableSource p mode name = variableSource q mode name := by
  unfold variableSource
  rw [same.declaration,capture_eq same,binder_eq same]

theorem footprints {p q : Plan roles} (same : Same p q) (mode exp) :
    footprint p mode exp = footprint q mode exp := by
  unfold footprint
  apply List.map_congr_left
  intro cell _
  exact variable_eq same cell.1 cell.2

theorem address {p q : Plan roles} (same : Same p q) (side : Side) (clause pos : Nat) (expr : Expr) :
    atCell p side clause pos expr = atCell q side clause pos expr := by
  unfold atCell key
  rw [same.seed,occurrence same,same.declaration,footprints same]

theorem argument_allocation {p q : Plan roles} (same : Same p q) (clause) :
    args p clause = args q clause := by
  funext i
  unfold args
  rw [frame_eq same,same.declaration,same.registry,same.interpretation]
  cases ha : clause.arguments[i.val]? with
  | none => rfl
  | some pat =>
    cases ht : GeneralNominalCenteredHeadMatExpressions.translate q.packet.registry.constructors q.packet.context.interpretation pat with
    | none => simp [ht]
    | some exp => simp only [ht]; rw [address same,address same]

theorem allocation_eq {p q : Plan roles} (same : Same p q) : allocation p = allocation q := by
  funext clause
  unfold allocation
  rw [argument_allocation same,frame_eq same,same.declaration]

theorem emissions_eq {p q : Plan roles} (same : Same p q) : emissions p = emissions q := by
  rcases p with ⟨⟨rp,cp,sp,dp,hp,bp⟩,ip,jp⟩
  rcases q with ⟨⟨rq,cq,sq,dq,hq,bq⟩,iq,jq⟩
  have reg : rp = rq := same.registry
  have decl : dp = dq := same.declaration
  subst rq; subst dq
  unfold emissions
  rw [occurrence same,capture_eq same,allocation_eq same]

theorem children_eq {p q : Plan roles} (same : Same p q) : children p = children q := by
  unfold children
  rw [emissions_eq same,frame_eq same]

theorem schema_eq {p q : Plan roles} (same : Same p q) : schema p = schema q := by
  unfold schema
  rw [emissions_eq same,same.registry,same.interpretation,same.declaration,occurrence same]

theorem actual_after_observation :
    children GeneralWhereVersionRootReport317.plan = [GeneralWhereVersionCase317.occ] ∧
    schema GeneralWhereVersionRootReport317.plan = schema GeneralLiveCompoundPostFrames316.rootPlan := by
  have same := GeneralWhereVersionRootReport317.same
  exact ⟨(children_eq same).symm.trans GeneralWhereVersionCase317.ordered_children,(schema_eq same).symm⟩

end Yulang.GeneralWhereVersionRecompile317
