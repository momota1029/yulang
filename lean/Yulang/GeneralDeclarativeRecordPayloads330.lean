import Yulang.GeneralDeclarativeRecordSpine330
import Yulang.GeneralDeclarativeRecordIntervals330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordPayloads330
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeRecordSpine330 (Spine was_named)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeRecordChannel330 (project shows addTrivial)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty record Subtype subtype_trans)
open CommonRoleCanonicalRows (Row)

/-- First visible exact field, not the printing order of a model's
assignment. A later same-label syntax occurrence cannot replace it. -/
inductive Field (key : Nat) : Row Expr → Expr → Prop where
  | here : Field key ((key,payload)::xs) payload
  | later : label ≠ key → Field key xs payload →
      Field key ((label,e)::xs) payload

theorem visible (seen : Field key raw payload) (terminal : Expr) (m : Assignment) :
    project key false [] (value (environment m) .actual (withTail raw terminal)) =
      some (value (environment m) .actual payload) := by
  induction seen with
  | here =>
    exact direct key false _ _
  | later different _ ih =>
    simp [withTail,value,record,project,shows,Ne.symm different,addTrivial,ih]

theorem payload_below {s : State} {p : Supported s done}
    (first : Spine (restriction p) a fs firstEnd)
    (last : Spine (restriction p) b gs lastEnd)
    (seen : Field key fs f) (also : Field key gs g)
    (m : Assignment) (valid : Models s m) (span : Subtype (m a).1 (m b).1) :
    Subtype (value (environment m) .actual f) (value (environment m) .actual g) := by
  have left := semantic (was_named first) m valid
  have right := semantic (was_named last) m valid
  exact projected_below key false (visible seen firstEnd m) (visible also lastEnd m)
    (subtype_trans left.2 (subtype_trans span right.1))

/-- Actual named or inline source payloads at three independently
supported record observations inherit the interval for every current
model. This works for any repeated label or remaining fields and
does not infer that an opaque/unknown centre has a source spine. -/
theorem all_mode {s : State} {p : Supported s done} (box : Bounds s arg)
    (lo : Spine (restriction p) arg.lower ls endL)
    (ce : Spine (restriction p) arg.center cs endC)
    (hi : Spine (restriction p) arg.upper us endU)
    (a : Field key ls left) (b : Field key cs middle) (c : Field key us right)
    (m : Assignment) (fits : Models s m) :
    Subtype (value (environment m) .actual left) (value (environment m) .actual middle) ∧
    Subtype (value (environment m) .actual middle) (value (environment m) .actual right) :=
  ⟨payload_below lo ce a b m fits (bound_sound m fits.1 box.1),
    payload_below ce hi b c m fits (bound_sound m fits.1 box.2)⟩


open CommonNominalFullCarrier (observeTy)
open CommonNominalFullDemand (Environment ProbeAt ProbeStep MaskedProbeStep)
open GeneralDeclarativeRecordChannel330 (channel)
open GeneralDeclarativeRecordProbe330 (read probe)

theorem has_field {x y b : Ty} (use : project key false [] y = some b)
    (below : Subtype x y) : ∃ mid, project key false [] x = some mid := by
  let env : Environment CommonNominalFullCarrier.Row := ⟨fun _ => .bottom,fun _ => []⟩
  have atUpper : ProbeAt Common.rowLe 0 env (observeTy 1 y) (channel false key .trivial) :=
    (read key 0 0 env _ _ .trivial false use).mpr (by
      cases h : observeTy 0 b <;> simp [ProbeAt,ProbeStep,MaskedProbeStep])
  have atMid := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 1) 0 env _ atUpper
  have result := (probe key 0 env (fun _ _ => True) x false [] .trivial).mp atMid
  cases printed : project key false [] x with
  | none => simp [printed,GeneralDeclarativeOpaqueChannel328.tests] at result
  | some mid => exact ⟨mid,rfl⟩

/-- Closed source spines at the two endpoints support each arbitrary
visible required field, even when there is no supported spine of
the centre. This is a payload observation in each admissible model;
it does not produce one uniform logical tail or a literal record. -/
theorem opaque_payload {s : State} {p : Supported s done} (box : Bounds s arg)
    (first : Spine (restriction p) arg.lower fs endL)
    (last : Spine (restriction p) arg.upper us endU)
    (seen : Field key fs f) (also : Field key us g) (m : Assignment) (valid : Models s m) :
    ∃ mid, project key false [] (m arg.center).1 = some mid ∧
      Subtype (value (environment m) .actual f) mid ∧
      Subtype mid (value (environment m) .actual g) := by
  have left := semantic (was_named first) m valid
  have right := semantic (was_named last) m valid
  have a := subtype_trans left.2 (bound_sound m valid.1 box.1)
  have b := subtype_trans (bound_sound m valid.1 box.2) right.1
  obtain ⟨mid,printed⟩ := has_field (visible also endU m) b
  exact ⟨mid,printed,projected_below key false (visible seen endL m) printed a,
    projected_below key false printed (visible also endU m) b⟩

end Yulang.GeneralDeclarativeRecordPayloads330
