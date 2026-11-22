import Yulang.GeneralDeclarativeRecordConsumption330
import Yulang.CommonNominalFullFiniteMaskOrder

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointRecord336
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeRecordSpine330 (Spine was_named)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open CommonRoleCanonicalRows (Row normalize normalize_unique)
open GeneralDeclarativeRecordPayloads330 (Field visible has_field)
open GeneralDeclarativeRecordConsumption330 (read_field)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (projected_below)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype Equivalent mask observeTy subtype_trans)

theorem mask_below (keys : List Nat) {a b : Ty} (h : Subtype a b) :
    Subtype (mask keys a) (mask keys b) :=
  fun d => CommonNominalFullDemand.producerLe_mask keys (h d)

theorem mask_equiv (keys : List Nat) {a b : Ty} (h : Equivalent a b) :
    Equivalent (mask keys a) (mask keys b) :=
  ⟨mask_below keys h.1,mask_below keys h.2⟩

/-- A record read consults the normalized ordered field lists at the
two supported endpoints, not the actual center row. The terminals can
differ: one endpoint may be width-open and the other exact-closed. -/
structure Read {s : State} (p : Supported s done) (arg : Capture)
    (keys : List Nat) (lower upper first last : Row Expr) (loEnd hiEnd : Expr) : Prop where
  valid : Bounds s arg
  distinct : keys.Nodup
  lo : Spine (restriction p) arg.lower lower loEnd
  hi : Spine (restriction p) arg.upper upper hiEnd
  displayedLow : order (normalize lower) keys = some first
  displayedHigh : order (normalize upper) keys = some last

def interp (m : Assignment) (code : Expr) : Ty :=
  value (environment m) .actual code

theorem labels {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue) :
    first.map Prod.fst = keys ∧ last.map Prod.fst = keys :=
  ⟨(exact_order (normalize_unique ls) r.displayedLow).1,
    (exact_order (normalize_unique us) r.displayedHigh).1⟩

theorem interval {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (m : Assignment) (fit : Models s m) :
    InInterval (interp m (withTail ls le)) (interp m (withTail us ue)) (m arg.center).1 := by
  let lo := semantic (was_named r.lo) m fit
  let hi := semantic (was_named r.hi) m fit
  let bounded := bounds_sound r.valid m fit
  exact ⟨subtype_trans lo.2 bounded.1,subtype_trans bounded.2 hi.1⟩

theorem field_interval {s : State} {p : Supported s done} (r : Read p arg keys ls us first last le ue)
    (inLo : (key,a) ∈ first) (inHi : (key,b) ∈ last) (m : Assignment) (fit : Models s m) :
    ∃ f, project key false [] (m arg.center).1 = some f ∧ InInterval (interp m a) (interp m b) f := by
  have v := interval r m fit
  have lo := visible (read_field r.displayedLow inLo) le m
  have hi := visible (read_field r.displayedHigh inHi) ue m
  obtain ⟨f,actual⟩ := has_field hi v.2
  exact ⟨f,actual,projected_below key false lo actual v.1,projected_below key false actual hi v.2⟩

/-- Removing the same captured labels on all three sides preserves the
actual residual interval. This is a semantic masked residual; an
ordinary symbolic name for it is a separate representation issue. -/
theorem residual_interval {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m : Assignment) (fit : Models s m) :
    InInterval (mask keys (interp m (withTail ls le)))
      (mask keys (interp m (withTail us ue))) (mask keys (m arg.center).1) :=
  ⟨mask_below keys (interval r m fit).1,mask_below keys (interval r m fit).2⟩

end Yulang.GeneralDeclarativeEndpointRecord336
