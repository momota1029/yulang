import Yulang.CommonPresence

/-!
# Passing exactly the remaining record demands to a common tail

The new optional observation changes the tail interface: in addition to field
tests, only nontrivial optional tests remain. A record head already discharges
the trivial optional test. Neither the head's label nor record-kind/role tests
are passed to its tail. The same relation is lifted at the same regular depth.
-/

namespace Yulang.CommonFinite

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

def RecordTailLe (leRow : Row → Row → Prop) (hidden : List Nat)
    (source target : Ty Row) : Prop :=
  (∀ rank env label, label ∉ hidden → ∀ obs,
    ProbeAt leRow rank env target (.field label obs) →
      ProbeAt leRow rank env source (.field label obs)) ∧
  (∀ rank env label, label ∉ hidden → ∀ obs, obs ≠ .trivial →
    ProbeAt leRow rank env target (.optional label obs) →
      ProbeAt leRow rank env source (.optional label obs))

theorem recordTailLe_refl (hidden : List Nat) (type : Ty Row) :
    RecordTailLe leRow hidden type type :=
  ⟨fun _ _ _ _ _ valid => valid, fun _ _ _ _ _ _ valid => valid⟩

theorem recordTailLe_trans (hidden : List Nat) {first middle last : Ty Row}
    (before : RecordTailLe leRow hidden first middle)
    (after : RecordTailLe leRow hidden middle last) : RecordTailLe leRow hidden first last :=
  ⟨fun rank env label visible obs valid =>
      before.1 rank env label visible obs (after.1 rank env label visible obs valid),
    fun rank env label visible obs nontrivial valid =>
      before.2 rank env label visible obs nontrivial
        (after.2 rank env label visible obs nontrivial valid)⟩

theorem recordTailLe_emptyRecord (hidden : List Nat) (source : Ty Row) :
    RecordTailLe leRow hidden source .emptyRecord := by
  constructor
  · intro rank env label visible obs accepted
    cases rank <;> exact False.elim accepted
  · intro rank env label visible obs nontrivial accepted
    cases rank <;> exact False.elim (nontrivial accepted)

theorem producerLe_record_iff (label : Nat) (first last rest tail : Ty Row) :
    ProducerLe leRow (.record label first rest) (.record label last tail) ↔
      ProducerLe leRow first last ∧ RecordTailLe leRow [label] rest tail := by
  constructor
  · intro below
    have projected := (producerLe_iff_probe _ _).mp below
    constructor
    · apply (producerLe_iff_probe _ _).mpr
      intro rank env obs valid
      have output := projected rank env (.field label obs)
      simp only [probeAt_record_field, ↓reduceIte] at output
      exact output valid
    · constructor
      · intro rank env current visible obs valid
        have different : current ≠ label := by simpa using visible
        have output := projected rank env (.field current obs)
        simp only [probeAt_record_field, different, ↓reduceIte] at output
        exact output valid
      · intro rank env current visible obs nontrivial valid
        have different : current ≠ label := by simpa using visible
        have output := projected rank env (.optional current obs)
        simp only [probeAt_record_optional, different, ↓reduceIte, nontrivial, or_false] at output
        exact output valid
  · rintro ⟨payload, fields, optional⟩
    apply (producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    cases obs with
    | field current inner =>
        by_cases same : current = label
        · subst current
          simp only [probeAt_record_field, ↓reduceIte] at accepted ⊢
          exact (producerLe_iff_probe _ _).mp payload rank env inner accepted
        · simp only [probeAt_record_field, same, ↓reduceIte] at accepted ⊢
          exact fields rank env current (by simpa using same) inner accepted
    | optional current inner =>
        by_cases same : current = label
        · subst current
          simp only [probeAt_record_optional, ↓reduceIte] at accepted ⊢
          exact (producerLe_iff_probe _ _).mp payload rank env inner accepted
        · simp only [probeAt_record_optional, same, ↓reduceIte] at accepted ⊢
          by_cases trivial : inner = .trivial
          · exact Or.inr trivial
          · exact Or.inl (optional rank env current (by simpa using same) inner trivial
              (accepted.resolve_right trivial))
    | _ => cases rank <;> exact accepted

theorem singleton_requirement_iff (label : Nat) (first last rest : Ty Row) :
    ProducerLe leRow (.record label first rest) (required label last) ↔
      ProducerLe leRow first last := by
  rw [required, producerLe_record_iff]
  exact and_iff_left (recordTailLe_emptyRecord [label] rest)

theorem recordTailLe_hidden_head_iff (hidden : List Nat) (label : Nat)
    (payload rest target : Ty Row) :
    RecordTailLe leRow (label :: hidden) (.record label payload rest) target ↔
      RecordTailLe leRow (label :: hidden) rest target := by
  constructor <;> intro below <;> constructor
  · intro rank env current visible obs accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_field, different, ↓reduceIte] using
      below.1 rank env current visible obs accepted
  · intro rank env current visible obs nontrivial accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    have output := below.2 rank env current visible obs nontrivial accepted
    simpa only [probeAt_record_optional, different, ↓reduceIte, nontrivial, or_false] using output
  · intro rank env current visible obs accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_field, different, ↓reduceIte] using
      below.1 rank env current visible obs accepted
  · intro rank env current visible obs nontrivial accepted
    have different : current ≠ label := fun same => visible (List.mem_cons.mpr (Or.inl same))
    simpa only [probeAt_record_optional, different, ↓reduceIte, nontrivial, or_false] using
      below.2 rank env current visible obs nontrivial accepted

theorem shadowed_head_equivalent (label : Nat) (payload hidden rest : Ty Row) :
    ProducerEq leRow (.record label payload (.record label hidden rest)) (.record label payload rest) := by
  constructor
  · exact (producerLe_record_iff _ _ _ _ _).mpr
      ⟨producerLe_refl _, (recordTailLe_hidden_head_iff [] label hidden rest rest).mpr
        (recordTailLe_refl _ _)⟩
  · apply (producerLe_record_iff _ _ _ _ _).mpr
    refine ⟨producerLe_refl _, ?_⟩
    constructor
    · intro rank env current visible obs accepted
      have different : current ≠ label := by simpa using visible
      simpa only [probeAt_record_field, different, ↓reduceIte] using accepted
    · intro rank env current visible obs nontrivial accepted
      have different : current ≠ label := by simpa using visible
      simpa only [probeAt_record_optional, different, ↓reduceIte, nontrivial, or_false] using accepted

/-- The old positive data-demand record recipe is not a producer identity,
even when the tail is below width. Its masked bottom accepts base demands that
no record constructor accepts. The constructor-tail compiler must use a
proved producer polynomial instead. -/
theorem record_not_naive_required_mask (label : Nat) (payload : Ty Row) :
    ¬ ProducerEq leRow (.record label payload .bottom)
      (.inter (required label payload) (.mask [label] .bottom)) := by
  intro same
  let env : Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have accepted : ProbeAt leRow 0 env
      (.inter (required label payload) (.mask [label] .bottom)) (.base .int) := by
    simp [ProbeAt, ProbeStep, MaskedProbeStep]
  have invalid := (producerLe_iff_probe _ _).mp same.1 0 env (.base .int) accepted
  exact invalid

end Yulang.CommonFinite

namespace Yulang.Common

def RecordTailLe (hidden : List Nat) (source target : Ty) : Prop :=
  ∀ depth, CommonFinite.RecordTailLe rowLe hidden (observeTy depth source) (observeTy depth target)

theorem common_record_iff (label : Nat) (first last rest tail : Ty) :
    Subtype (record label first rest) (record label last tail) ↔
      Subtype first last ∧ RecordTailLe [label] rest tail := by
  constructor
  · intro below
    have split := fun depth => (CommonFinite.producerLe_record_iff label _ _ _ _).mp (below depth)
    exact ⟨fun depth => (split (depth + 1)).1, fun depth => (split depth).2⟩
  · rintro ⟨payload, remaining⟩ depth
    exact (CommonFinite.producerLe_record_iff label _ _ _ _).mpr
      ⟨quote_observe_le payload depth, remaining depth⟩

theorem common_singleton_requirement_iff (label : Nat) (first last rest : Ty) :
    Subtype (record label first rest) (required label last) ↔ Subtype first last := by
  rw [required, common_record_iff]
  exact and_iff_left (fun depth => CommonFinite.recordTailLe_emptyRecord [label] _)

theorem common_shadowed_head_equivalent (label : Nat) (payload hidden rest : Ty) :
    Equivalent (record label payload (record label hidden rest)) (record label payload rest) :=
  ⟨fun _ => (CommonFinite.shadowed_head_equivalent label _ _ _).1,
    fun _ => (CommonFinite.shadowed_head_equivalent label _ _ _).2⟩

theorem common_record_not_naive_required_mask (label : Nat) (payload : Ty) :
    ¬ Equivalent (record label payload .bottom)
      (.inter (required label payload) (mask [label] .bottom)) := by
  intro same
  exact CommonFinite.record_not_naive_required_mask label _ ⟨same.1 0, same.2 0⟩

end Yulang.Common
