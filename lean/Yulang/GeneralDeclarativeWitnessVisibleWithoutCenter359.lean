import Yulang.GeneralDeclarativeWitnessOpenFixture359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessVisibleWithoutCenter359
open CommonNominalFullCarrier (Ty Row Subtype observeTy record subtype_trans)
open CommonNominalFullDemand (ProbeAt Observation Environment producerLe_iff_probe)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessOpenSpine359 (Head Read sem read_in_model)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeExactDelete337 (subtract)

def VisibleAt (typ : Ty) (depth rank : Nat) (env : Environment Row) (label : Nat) (test : Observation Row) : Prop :=
  ProbeAt Common.rowLe rank env (observeTy depth typ) (.field label test)

theorem visible_monotone {a b} (h : Subtype a b) :
    VisibleAt b depth rank env label probe → VisibleAt a depth rank env label probe :=
  (producerLe_iff_probe _ _).mp (h depth) rank env _

theorem written_field_is_present (key : Nat) (payload rest : Ty) (depth rank : Nat) (env : Environment Row) :
    VisibleAt (record key payload rest) (depth+1) rank env key .trivial := by
  cases rank <;> simp [VisibleAt,ProbeAt,observeTy,record,CommonNominalSyntax.Layer.evalAt,
    CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]

/-- The actual center has all common visible observations of the
authored upper field, and no observation outside the lower one.
Neither this statement nor its proof guesses a center expression. -/
theorem actual_visible_field_without_center {source : Source} {s : State} {cap : Capture} {lo hi : Head}
    (lower : Read source s cap.lower lo.path) (upper : Read source s cap.upper hi.path)
    (ordered : Bound s.normal cap.lower cap.center ∧ Bound s.normal cap.center cap.upper)
    (m : Assignment) (fit : Models s m) :
    ∀ depth rank (env : Environment Row),
      VisibleAt (m cap.center).1 (depth+1) rank env hi.label .trivial ∧
      ∀ test : Observation Row,
        (VisibleAt (sem m (hi.path.expand cap.upper)) (depth+1) rank env hi.label test →
          VisibleAt (m cap.center).1 (depth+1) rank env hi.label test) ∧
        (VisibleAt (m cap.center).1 (depth+1) rank env hi.label test →
          VisibleAt (sem m (lo.path.expand cap.lower)) (depth+1) rank env hi.label test) := by
  intro depth rank env
  have a := read_in_model lower m fit
  have b := read_in_model upper m fit
  have below := subtype_trans a.2 (bound_sound m fit.1 ordered.1)
  have above := subtype_trans (bound_sound m fit.1 ordered.2) b.1
  exact ⟨visible_monotone above (written_field_is_present hi.label
    (sem m hi.payload) (sem m hi.tail) depth rank env),
    fun _ => ⟨visible_monotone above,visible_monotone below⟩⟩

open GeneralDeclarativeWitnessOpenFixture359
  (capture current model_fits low high reads_both_independent_inline_heads)
open GeneralDeclarativeWitnessRecordWidthFixture359 (model lowRest highRest)

theorem actual_strict_source_has_field_in_every_center (m)
    (fit : Models current m) (depth rank : Nat) (env : Environment Row) :
    VisibleAt (m capture.center).1 (depth+1) rank env 7 .trivial :=
  (actual_visible_field_without_center
    (GeneralDeclarativeWitnessOpenSpine359.check_exact.mp reads_both_independent_inline_heads.1)
    (GeneralDeclarativeWitnessOpenSpine359.check_exact.mp reads_both_independent_inline_heads.2)
    ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    m fit depth rank env).1

private def env : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
/-- This optional probe distinguishes absent from unresolved width in the
concrete deleted remainders below; it is not a general absence predicate. -/
def AbsenceSensitive7 (t : Ty) : Prop :=
  ProbeAt Common.rowLe 0 env (observeTy 1 t) (.optional 7 (.base .int))

theorem removal_keeps_exact_absence_only_when_observed :
    Models current (model false) ∧ Models current (model true) ∧
    AbsenceSensitive7 (subtract [7] (model false capture.center).1) ∧
    ¬AbsenceSensitive7 (subtract [7] (model true capture.center).1) := by
  refine ⟨model_fits false,model_fits true,?_,?_⟩
  · change AbsenceSensitive7 lowRest
    simp [AbsenceSensitive7,lowRest,CommonNominalFullCarrier.exactEmpty,ProbeAt,observeTy,record,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]
  · change ¬AbsenceSensitive7 highRest
    simp [AbsenceSensitive7,highRest,CommonNominalFullCarrier.emptyRecord,ProbeAt,observeTy,record,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]

end Yulang.GeneralDeclarativeWitnessVisibleWithoutCenter359
