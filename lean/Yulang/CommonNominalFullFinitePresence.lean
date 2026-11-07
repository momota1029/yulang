import Yulang.CommonNominalFullFiniteMask

/-!
# Concrete presence laws in the finite common carrier

These are producer-demand statements. The strict runtime image remains an
independent interpretation; in particular a producer equality below does not
remove the evaluation of a fallback or assert inhabitation of either operand.
-/

namespace Yulang.CommonNominalFullDemand

universe u
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}

theorem exactEmpty_below_width :
    ProducerLe leRow (.exactEmpty : Ty Row) .emptyRecord := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]

/-- The distinction is semantic: known absence meets an optional impossible
payload requirement, whereas arbitrary width does not. -/
theorem width_not_below_exactEmpty :
    ¬ ProducerLe leRow (.emptyRecord : Ty Row) .exactEmpty := by
  intro below
  let env : Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have valid : ProbeAt leRow 0 env .exactEmpty (.optional 0 .impossible) := by
    simp [ProbeAt, ProbeStep, MaskedProbeStep]
  have invalid := (producerLe_iff_probe _ _).mp below 0 env (.optional 0 .impossible) valid
  simp [ProbeAt, ProbeStep, MaskedProbeStep] at invalid

theorem exactEmpty_not_equivalent_width :
    ¬ ProducerEq leRow (.exactEmpty : Ty Row) .emptyRecord :=
  fun same => width_not_below_exactEmpty same.2

theorem required_as_width_tail (label : Nat) (payload : Ty Row) :
    CommonNominalFinite.Ty.record label payload .emptyRecord = required label payload := rfl

@[simp] theorem probeAt_record_field (rank : Nat) (env : Environment Row)
    (current label : Nat) (payload rest : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.record current payload rest) (.field label obs) ↔
      if label = current then ProbeAt leRow rank env payload obs
      else ProbeAt leRow rank env rest (.field label obs) := by
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

@[simp] theorem probeAt_record_optional (rank : Nat) (env : Environment Row)
    (current label : Nat) (payload rest : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.record current payload rest) (.optional label obs) ↔
      if label = current then ProbeAt leRow rank env payload obs
      else ProbeAt leRow rank env rest (.optional label obs) ∨ obs = .trivial := by
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

/-- This is an independent recursive one-observation decomposition, not a
finite complete branch inspector for an arbitrary target type. -/
@[simp] theorem probeAt_default_field (rank : Nat) (env : Environment Row)
    (current label : Nat) (source fallback : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.recordDefault current source fallback) (.field label obs) ↔
      if label = current then
        ProbeAt leRow rank env source (.optional label obs) ∧
          (ProbeAt leRow rank env source (.field label .trivial) ∨
            ProbeAt leRow rank env fallback obs)
      else ProbeAt leRow rank env source (.field label obs) := by
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

@[simp] theorem probeAt_default_optional (rank : Nat) (env : Environment Row)
    (current label : Nat) (source fallback : Ty Row) (obs : Observation Row) :
    ProbeAt leRow rank env (.recordDefault current source fallback) (.optional label obs) ↔
      (if label = current then
        ProbeAt leRow rank env source (.optional label obs) ∧
          (ProbeAt leRow rank env source (.field label .trivial) ∨
            ProbeAt leRow rank env fallback obs)
      else ProbeAt leRow rank env source (.optional label obs)) ∨ obs = .trivial := by
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem recordDefault_below_width (label : Nat) (source fallback : Ty Row) :
    ProducerLe leRow (.recordDefault label source fallback) .emptyRecord := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> simp_all

/-- Known absence chooses the fallback for the selected field while retaining
all absence information about unrelated fields. -/
theorem default_exactEmpty (label : Nat) (fallback : Ty Row) :
    ProducerEq leRow (.recordDefault label .exactEmpty fallback)
      (.record label fallback .exactEmpty) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals
    intro same _
    cases same
    exact maskedProbeStep_trivial [] fallback

/-- Known presence keeps the whole producer record, including its tail.
This equality is independent of strict fallback evaluation in DataReadout. -/
theorem default_present_record (label : Nat) (payload rest fallback : Ty Row) :
    ProducerEq leRow (.recordDefault label (.record label payload rest) fallback)
      (.record label payload rest) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> simp_all

/-- Whole default is monotone in both operands under the concrete producer
order. No runtime nonemptiness law is assumed or inferred. -/
theorem producerLe_recordDefault (label : Nat) {source source' fallback fallback' : Ty Row}
    (base : ProducerLe leRow source source') (default : ProducerLe leRow fallback fallback') :
    ProducerLe leRow (.recordDefault label source fallback)
      (.recordDefault label source' fallback') := by
  have base := (producerLe_iff_probe _ _).mp base
  have default := (producerLe_iff_probe _ _).mp default
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  have base := base rank env
  have default := default rank env
  cases rank <;> cases obs <;> simp_all [ProbeAt, ProbeStep, MaskedProbeStep]
  all_goals split <;> simp_all
  all_goals first
    | exact Or.imp (base _) id accepted
    | exact Or.imp (base _) (default _) accepted.2
    | exact Or.imp (fun valid => ⟨base _ valid.1, Or.imp (base _) (default _) valid.2⟩) id accepted

theorem producerEq_recordDefault (label : Nat) {source source' fallback fallback' : Ty Row}
    (base : ProducerEq leRow source source') (default : ProducerEq leRow fallback fallback') :
    ProducerEq leRow (.recordDefault label source fallback)
      (.recordDefault label source' fallback') :=
  ⟨producerLe_recordDefault label base.1 default.1,
    producerLe_recordDefault label base.2 default.2⟩

end Yulang.CommonNominalFullDemand

namespace Yulang.CommonNominalFullDemand

/-- At a known absent field the default supplies a required value and retains
absence information for every other field. -/
theorem default_required_absence {Row : Type u} {leRow : Row → Row → Prop}
    (label : Nat) (fallback : Ty Row) :
    ProducerEq leRow (.recordDefault label .exactEmpty fallback)
      (.record label fallback .exactEmpty) := default_exactEmpty label fallback

end Yulang.CommonNominalFullDemand
