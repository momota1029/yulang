import YulangClosure.NativeRowRepresentative
import YulangClosure.NativeContextReadback

/-!
Discharge the two representative-map premises of the existing shared Context
driver's merge event from successful raw parent-pointer histories.  Readback
is an execution of the actual lookup relation, not a canonical-map law.
The two forests remain separate.  This does not extract those histories from
Rust, establish a rollback cut, or count native generation increments.
-/
namespace YulangClosure.NativeRepresentativeReadback

namespace F
export NativeRowRepresentative (Forest Certificate Lookup Run empty)
end F

/-- A successful forward interval in one row-kind forest, with its actual
generated prefix. No representative equation is included in these fields. -/
structure Interval where
  before : NativeRowRepresentative.Forest
  after : NativeRowRepresentative.Forest
  generated : NativeRowRepresentative.Run NativeRowRepresentative.empty before
  operations : NativeRowRepresentative.Run before after

/-- Every observed representative is returned by the raw pointer lookup loop.
Rows outside the vector are included, with the native identity convention. -/
def Readback (forest : NativeRowRepresentative.Forest) (map : Nat → Nat) : Prop :=
  ∀ row, NativeRowRepresentative.Lookup forest row (map row)

theorem certificate_readback {forest : NativeRowRepresentative.Forest}
    (certificate : NativeRowRepresentative.Certificate forest) : Readback forest certificate.root :=
  NativeRowRepresentative.lookup_terminates certificate

theorem readback_unique {forest : NativeRowRepresentative.Forest} {first second : Nat → Nat}
    (left : Readback forest first) (right : Readback forest second) : first = second := by
  funext row
  exact NativeRowRepresentative.lookup_unique (left row) (right row)

/-- The law formerly supplied to Step.merge follows from actual lookup and
birth/link/compression events. Neither input assumes idempotence/absorption. -/
theorem readback_absorbs (interval : Interval) {before after : Nat → Nat}
    (old : Readback interval.before before) (current : Readback interval.after after) :
    ∀ row, after (before row) = after row := by
  obtain ⟨first⟩ := NativeRowRepresentative.generated_certificate interval.generated
  obtain ⟨last, absorbs⟩ := NativeRowRepresentative.run_constructs first interval.operations
  have firstMap := readback_unique old (certificate_readback first)
  have lastMap := readback_unique current (certificate_readback last)
  simpa only [firstMap, lastMap] using absorbs

/-- Construct an observed final map and its law, rather than require callers
to supply a final representative map or a certificate. -/
theorem construct_readback (interval : Interval) {before : Nat → Nat}
    (old : Readback interval.before before) :
    ∃ after : Nat → Nat, Readback interval.after after ∧
      ∀ row, after (before row) = after row := by
  obtain ⟨first⟩ := NativeRowRepresentative.generated_certificate interval.generated
  obtain ⟨last, absorbs⟩ := NativeRowRepresentative.run_constructs first interval.operations
  refine ⟨last.root, certificate_readback last, ?_⟩
  have same := readback_unique old (certificate_readback first)
  simpa only [same] using absorbs

def install {t : NativeContextExpansion.Tables} (s : NativeContextReadback.State t)
    (effect value : Nat → Nat) : NativeContextReadback.State t :=
  { s with effectMap := effect, valueMap := value, generation := s.generation + 1 }

/-- An actual existing driver event, on the same state and exact two maps.
The settling guard is retained; table/memo/owner/control payload is untouched. -/
theorem raw_merge_event {t : NativeContextExpansion.Tables} (s : NativeContextReadback.State t)
    (effectRows valueRows : Interval) (effect value : Nat → Nat)
    (oldEffect : Readback effectRows.before s.effectMap)
    (oldValue : Readback valueRows.before s.valueMap)
    (newEffect : Readback effectRows.after effect)
    (newValue : Readback valueRows.after value) (settling : s.settling = true) :
    NativeContextReadback.Step t s (install s effect value) :=
  .merge s effect value settling (readback_absorbs effectRows oldEffect newEffect)
    (readback_absorbs valueRows oldValue newValue)

/-- No arbitrary after-map or absorption premise remains in this construction. -/
theorem construct_merge_event {t : NativeContextExpansion.Tables}
    (s : NativeContextReadback.State t) (effectRows valueRows : Interval)
    (oldEffect : Readback effectRows.before s.effectMap)
    (oldValue : Readback valueRows.before s.valueMap) (settling : s.settling = true) :
    ∃ effect value : Nat → Nat,
      Readback effectRows.after effect ∧ Readback valueRows.after value ∧
      NativeContextReadback.Step t s (install s effect value) := by
  obtain ⟨effect, readEffect, _⟩ := construct_readback effectRows oldEffect
  obtain ⟨value, readValue, _⟩ := construct_readback valueRows oldValue
  exact ⟨effect, value, readEffect, readValue,
    raw_merge_event s effectRows valueRows effect value oldEffect oldValue readEffect readValue settling⟩

/-- Extend the already reachable SAME shared Context/drain history.  The
settlement frame and all owner/memo/processed-work invariants follow from
that history; no independent completion witness is introduced. -/
theorem construct_merge_history {t : NativeContextExpansion.Tables}
    {s : NativeContextReadback.State t}
    (history : NativeContextReadback.Run t (NativeContextReadback.initial t) s)
    (effectRows valueRows : Interval)
    (oldEffect : Readback effectRows.before s.effectMap)
    (oldValue : Readback valueRows.before s.valueMap) (settling : s.settling = true) :
    ∃ effect value : Nat → Nat,
      Readback effectRows.after effect ∧ Readback valueRows.after value ∧
      NativeContextReadback.Run t (NativeContextReadback.initial t) (install s effect value) ∧
      NativeContextReadback.Invariant (install s effect value) ∧
      (∃ f fs, (install s effect value).control.frames = f :: fs ∧
        f.phase = .working ∧ f.current = none) ∧
      (install s effect value).control = s.control ∧
      (install s effect value).memo = s.memo ∧
      (install s effect value).owners = s.owners ∧
      (install s effect value).relations = s.relations ∧
      (install s effect value).tasks = s.tasks ∧
      (install s effect value).generation = s.generation + 1 := by
  obtain ⟨effect, value, effectRead, valueRead, event⟩ :=
    construct_merge_event s effectRows valueRows oldEffect oldValue settling
  have extended := NativeContextReadback.Run.snoc history event
  refine ⟨effect, value, effectRead, valueRead, extended,
    NativeContextReadback.reachable_invariant extended, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact NativeContextReadback.merge_session_has_actual_cut extended settling

/-- One actual successful Effect root link: the Value forest/map stays fixed,
and the source/target are the representatives read from the two raw operands.
Equal roots are a native no-op and are deliberately excluded from this event. -/
theorem single_effect_merge_event {t : NativeContextExpansion.Tables}
    (s : NativeContextReadback.State t)
    (effects values : NativeRowRepresentative.Forest)
    (generatedEffects : NativeRowRepresentative.Run NativeRowRepresentative.empty effects)
    (generatedValues : NativeRowRepresentative.Run NativeRowRepresentative.empty values)
    (effectRead : Readback effects s.effectMap) (valueRead : Readback values s.valueMap)
    (copy parent : Nat) (copyInside : copy < effects.size) (parentInside : parent < effects.size)
    (different : s.effectMap copy ≠ s.effectMap parent) (settling : s.settling = true) :
    ∃ effect : Nat → Nat,
      Readback (NativeRowRepresentative.write effects (s.effectMap copy) (s.effectMap parent)) effect ∧
      NativeContextReadback.Step t s (install s effect s.valueMap) := by
  let changed : Interval := ⟨effects,
    NativeRowRepresentative.write effects (s.effectMap copy) (s.effectMap parent),
    generatedEffects, .snoc (.nil _) (.merge effects copy parent _ _ copyInside parentInside
      (effectRead copy) (effectRead parent) different)⟩
  let unchanged : Interval := ⟨values, values, generatedValues, .nil _⟩
  obtain ⟨effect, readback, absorbs⟩ := construct_readback changed effectRead
  exact ⟨effect, readback,
    .merge s effect s.valueMap settling absorbs (readback_absorbs unchanged valueRead valueRead)⟩

/-- The corresponding Value root link preserves the Effect forest/map. -/
theorem single_value_merge_event {t : NativeContextExpansion.Tables}
    (s : NativeContextReadback.State t)
    (effects values : NativeRowRepresentative.Forest)
    (generatedEffects : NativeRowRepresentative.Run NativeRowRepresentative.empty effects)
    (generatedValues : NativeRowRepresentative.Run NativeRowRepresentative.empty values)
    (effectRead : Readback effects s.effectMap) (valueRead : Readback values s.valueMap)
    (copy parent : Nat) (copyInside : copy < values.size) (parentInside : parent < values.size)
    (different : s.valueMap copy ≠ s.valueMap parent) (settling : s.settling = true) :
    ∃ value : Nat → Nat,
      Readback (NativeRowRepresentative.write values (s.valueMap copy) (s.valueMap parent)) value ∧
      NativeContextReadback.Step t s (install s s.effectMap value) := by
  let unchanged : Interval := ⟨effects, effects, generatedEffects, .nil _⟩
  let changed : Interval := ⟨values,
    NativeRowRepresentative.write values (s.valueMap copy) (s.valueMap parent),
    generatedValues, .snoc (.nil _) (.merge values copy parent _ _ copyInside parentInside
      (valueRead copy) (valueRead parent) different)⟩
  obtain ⟨value, readback, absorbs⟩ := construct_readback changed valueRead
  exact ⟨value, readback,
    .merge s s.effectMap value settling (readback_absorbs unchanged effectRead effectRead) absorbs⟩

/-- Native-style compression changes no observed representative. It requires
no driver merge event or generation advance; its fuel is a constructed ghost
termination witness, not a new native resource bound. -/
theorem compression_keeps_readback {forest : NativeRowRepresentative.Forest} {map : Nat → Nat}
    (generated : NativeRowRepresentative.Run NativeRowRepresentative.empty forest)
    (readback : Readback forest map) (row : Nat) (inside : row < forest.size) :
    ∃ fuel after, NativeRowRepresentative.compress forest fuel row = some after ∧ Readback after map := by
  obtain ⟨before⟩ := NativeRowRepresentative.generated_certificate generated
  obtain ⟨after, executed, certificate, roots, _⟩ :=
    NativeRowRepresentative.compress_constructs before (fuel := before.height + 1) (by omega) inside
  refine ⟨before.height + 1, after, executed, ?_⟩
  have same := readback_unique readback (certificate_readback before)
  rw [same, ← roots]
  exact certificate_readback certificate

end YulangClosure.NativeRepresentativeReadback
