import Yulang.GeneralDeclarativeCompoundSources338
import Yulang.GeneralDeclarativeExactDeleteAuth337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundOpenPrefix338
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeCompoundSources338 (Anchors Anchored)
open GeneralDeclarativeCompoundEndpoints338 (order_iff)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordConsumption330 (read_field)
open GeneralDeclarativeRecordPayloads330 (visible has_field)
open GeneralDeclarativeRecordIntervals330 (projected_below)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeExactDelete337 (subtract monotone)
open CommonRoleCanonicalRows (Row normalize normalize_unique)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)

/-- Read only the author's visible finite prefix; its residual RHS is
an arbitrary original expression, not a new terminal judgment. -/
structure Read {s : State} (p : Supported s done) (arg : GeneralDeclarativeWhere319.Capture)
    (keys : List Nat) (ls us first last : Row Expr) (le ue : Expr) : Prop where
  bound : Bounds s arg
  anchors : Anchors (restriction p) arg (withTail ls le) (withTail us ue)
  unique : keys.Nodup
  low : order (normalize ls) keys = some first
  high : order (normalize us) keys = some last

theorem from_visible {s : State} {p : Supported s done}
    (bounds : Bounds s arg) (source : Anchors (restriction p) arg (withTail ls le) (withTail us ue))
    (unique : keys.Nodup)
    (low : ∀ k ∈ keys, ∃ l, (k,l) ∈ normalize ls)
    (high : ∀ k ∈ keys, ∃ u, (k,u) ∈ normalize us) :
    ∃ first last, Read p arg keys ls us first last le ue := by
  obtain ⟨first,lo⟩ := (order_iff (normalize_unique ls) keys).mpr low
  obtain ⟨last,hi⟩ := (order_iff (normalize_unique us) keys).mpr high
  exact ⟨first,last,bounds,source,unique,lo,hi⟩

theorem authorized {s : State} {p : Supported s done}
    (located : Anchored (restriction p) n e) (m : Assignment) (fit : Models s m) :
    Equivalent (m n).1 (interp m e) := by
  obtain ⟨_,same,found⟩ := located
  have trust := restrict_models p m fit
  exact eqv_trans (alias_sound same m trust) (trust.2 _ found)

theorem interval {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (m : Assignment) (fit : Models s m) :
    InInterval (interp m (withTail ls le)) (interp m (withTail us ue)) (m arg.center).1 := by
  have a := authorized r.anchors.1 m fit
  have b := authorized r.anchors.2 m fit
  have valid := bounds_sound r.bound m fit
  exact ⟨subtype_trans a.2 valid.1,subtype_trans valid.2 b.1⟩

/-- The visible field's true actual center is between the two authored
payloads even when neither outer residual has a supported terminal. -/
theorem field_interval {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (lower : (key,a) ∈ first) (upper : (key,b) ∈ last) (m : Assignment) (fit : Models s m) :
    ∃ actual, project key false [] (m arg.center).1 = some actual ∧
      InInterval (interp m a) (interp m b) actual := by
  have box := interval r m fit
  have lo := visible (read_field r.low lower) le m
  have hi := visible (read_field r.high upper) ue m
  obtain ⟨actual,known⟩ := has_field hi box.2
  exact ⟨actual,known,projected_below key false lo known box.1,projected_below key false known hi box.2⟩

def residuals (keys : List Nat) (m : Assignment) (arg : GeneralDeclarativeWhere319.Capture) :
    Ty × Ty × Ty :=
  (subtract keys (m arg.lower).1,subtract keys (m arg.center).1,subtract keys (m arg.upper).1)

/-- Even without an ordinary literal residual RHS, all three endpoint
values can be computed. They satisfy the exact interval. This is a
value-side receipt, not authorization to fabricate a source row. -/
theorem residual_interval {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (m : Assignment) (fit : Models s m) :
    let v := residuals keys m arg
    InInterval v.1 v.2.2 v.2.1 := by
  have held := bounds_sound r.bound m fit
  exact ⟨monotone keys held.1,monotone keys held.2⟩

theorem residual_authorized {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (m : Assignment) (fit : Models s m) :
    Equivalent (residuals keys m arg).1 (subtract keys (interp m (withTail ls le))) ∧
      Equivalent (residuals keys m arg).2.2 (subtract keys (interp m (withTail us ue))) :=
  ⟨GeneralDeclarativeExactDelete337.congruent keys (authorized r.anchors.1 m fit),
    GeneralDeclarativeExactDelete337.congruent keys (authorized r.anchors.2 m fit)⟩

open CommonNominalFullCarrier (record exactEmpty)
open GeneralDeclarativeExampleSource320 (int)

/-- It is not safe to reuse the untouched syntax underneath a visible
prefix: a late shadow of the captured key would become observable.
This distinguishes two ordinary values, not two resolver verdicts. -/
theorem a_hidden_shadow_cannot_resume :
    subtract [7] (record 7 int (record 7 int exactEmpty)) = exactEmpty ∧
      ¬ Equivalent (subtract [7] (record 7 int (record 7 int exactEmpty))) (record 7 int exactEmpty) := by
  have removed : subtract [7] (record 7 int (record 7 int exactEmpty)) = exactEmpty := rfl
  refine ⟨removed,?_⟩
  rw [removed]
  intro same
  have read : project 7 false [] (record 7 int exactEmpty) = some int :=
    GeneralDeclarativeRecordIntervals330.direct 7 false _ _
  obtain ⟨middle,exposed⟩ := has_field read same.1
  change none = some middle at exposed
  cases exposed

end Yulang.GeneralDeclarativeCompoundOpenPrefix338
