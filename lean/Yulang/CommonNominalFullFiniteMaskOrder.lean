import Yulang.CommonNominalFullFiniteMask

/-!
# Outer field masks respect the concrete producer order

A hidden field probe is recovered from a fresh label outside the finite outer
record/default/mask spine. Payloads are irrelevant to that fresh root probe.
Thus forgetting a head never reveals information absent from the complete
unmasked demand family. This supplies congruence, not a new semantic axiom.
-/

namespace Yulang.CommonNominalFullDemand

universe u
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {argumentOrder : Ty Row → Ty Row → Prop}

/-- Labels behind a payload boundary do not influence an outer mask. -/
def outerLabels : Ty Row → List Nat
  | .union first last | .inter first last => outerLabels first ++ outerLabels last
  | .record label _ tail | .recordDefault label tail _ => label :: outerLabels tail
  | .mask hidden type => hidden ++ outerLabels type
  | _ => []

private def freshLabel : List Nat → Nat
  | [] => 0
  | label :: rest => max (label + 1) (freshLabel rest)

private theorem label_lt_fresh (names : List Nat) (label : Nat) (member : label ∈ names) :
    label < freshLabel names := by
  induction names with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self label) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih tail) (Nat.le_max_right _ _)

private theorem fresh_not_mem (names : List Nat) : freshLabel names ∉ names :=
  fun member => Nat.lt_irrefl _ (label_lt_fresh names _ member)

/-- At one queried label only that label's hidden status matters. This
simultaneous statement retains default's optional and required source probes. -/
theorem maskedProbeStep_query_congr (type : Ty Row) (query : Nat) (obs : Observation Row)
    (first last : List Nat) (same : query ∈ first ↔ query ∈ last) :
    (MaskedProbeStep leRow env argumentOrder first type (.field query obs) ↔
      MaskedProbeStep leRow env argumentOrder last type (.field query obs)) ∧
    (MaskedProbeStep leRow env argumentOrder first type (.optional query obs) ↔
      MaskedProbeStep leRow env argumentOrder last type (.optional query obs)) := by
  induction type using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing first last query obs with
  | union a b iha ihb =>
      exact ⟨and_congr (iha query obs first last same).1 (ihb query obs first last same).1,
        and_congr (iha query obs first last same).2 (ihb query obs first last same).2⟩
  | inter a b iha ihb =>
      exact ⟨or_congr (iha query obs first last same).1 (ihb query obs first last same).1,
        or_congr (iha query obs first last same).2 (ihb query obs first last same).2⟩
  | record current payload tail ihp iht =>
      have fields := iht query obs first last same
      by_cases named : query = current
      · subst current
        by_cases member : query ∈ first
        · have lastMember := same.mp member
          simp [MaskedProbeStep, member, lastMember, fields.1, fields.2]
        · have lastMember : query ∉ last := fun h => member (same.mpr h)
          simp [MaskedProbeStep, member, lastMember]
      · simpa [MaskedProbeStep, named] using ⟨fields.1, or_congr fields.2 Iff.rfl⟩
  | recordDefault current source fallback ihs ihf =>
      have fields := ihs query obs first last same
      have present := ihs query .trivial first last same
      by_cases named : query = current
      · subst current
        by_cases member : query ∈ first
        · have lastMember := same.mp member
          simp [MaskedProbeStep, member, lastMember, fields.1, fields.2]
        · have lastMember : query ∉ last := fun h => member (same.mpr h)
          simp [MaskedProbeStep, member, lastMember, fields.2, present.1]
      · simpa [MaskedProbeStep, named] using ⟨fields.1, or_congr fields.2 Iff.rfl⟩
  | mask hidden type ih =>
      apply ih query obs (first ++ hidden) (last ++ hidden)
      simp only [List.mem_append, same]
  | exactEmpty => simp [MaskedProbeStep, same]
  | nil | cons | inl | inr => trivial
  | _ => simp [MaskedProbeStep]

/-- Required and nontrivial optional probes on a hidden field see only the
unconstrained residual tail, exactly as a fresh unmentioned field does. -/
theorem maskedProbeStep_hidden_query (type : Ty Row) (query fresh : Nat)
    (hidden : List Nat) (member : query ∈ hidden) (unused : fresh ∉ outerLabels type)
    (obs : Observation Row) (nontrivial : obs ≠ .trivial) :
    (MaskedProbeStep leRow env argumentOrder hidden type (.field query obs) ↔
      ProbeStep leRow env argumentOrder type (.field fresh .impossible)) ∧
    (MaskedProbeStep leRow env argumentOrder hidden type (.optional query obs) ↔
      ProbeStep leRow env argumentOrder type (.field fresh .impossible)) := by
  induction type using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing hidden with
  | union a b iha ihb =>
      have missing : fresh ∉ outerLabels a ∧ fresh ∉ outerLabels b := by
        simpa only [outerLabels, List.mem_append, not_or] using unused
      have first := iha hidden member missing.1
      have last := ihb hidden member missing.2
      exact ⟨and_congr first.1 last.1, and_congr first.2 last.2⟩
  | inter a b iha ihb =>
      have missing : fresh ∉ outerLabels a ∧ fresh ∉ outerLabels b := by
        simpa only [outerLabels, List.mem_append, not_or] using unused
      have first := iha hidden member missing.1
      have last := ihb hidden member missing.2
      exact ⟨or_congr first.1 last.1, or_congr first.2 last.2⟩
  | record current payload tail ihp iht =>
      have missing : fresh ≠ current ∧ fresh ∉ outerLabels tail := by
        simpa only [outerLabels, List.mem_cons, not_or] using unused
      have removed : ¬ (query = current ∧ current ∉ hidden) := by
        rintro ⟨rfl, visible⟩
        exact visible member
      simpa [ProbeStep, MaskedProbeStep, removed, missing.1, nontrivial] using
        iht hidden member missing.2
  | recordDefault current source fallback ihs ihf =>
      have missing : fresh ≠ current ∧ fresh ∉ outerLabels source := by
        simpa only [outerLabels, List.mem_cons, not_or] using unused
      have removed : ¬ (query = current ∧ current ∉ hidden) := by
        rintro ⟨rfl, visible⟩
        exact visible member
      simpa [ProbeStep, MaskedProbeStep, removed, missing.1, nontrivial] using
        ihs hidden member missing.2
  | mask more type ih =>
      have missing : fresh ∉ more ∧ fresh ∉ outerLabels type := by
        simpa only [outerLabels, List.mem_append, not_or] using unused
      have inner := ih (hidden ++ more) (List.mem_append.mpr (Or.inl member)) missing.2
      have erase := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) type fresh .impossible more []
        (by simp [missing.1])).1
      exact ⟨inner.1.trans erase.symm, inner.2.trans erase.symm⟩
  | nil | cons | inl | inr => trivial
  | _ => simp [ProbeStep, MaskedProbeStep, member, nontrivial]

/-- Required probes also allow a trivial payload. The residual tail cannot
inspect that payload after all matching heads have been removed. -/
theorem maskedProbeStep_hidden_field (type : Ty Row) (query fresh : Nat)
    (hidden : List Nat) (member : query ∈ hidden) (unused : fresh ∉ outerLabels type)
    (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden type (.field query obs) ↔
      ProbeStep leRow env argumentOrder type (.field fresh .impossible) := by
  induction type using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing hidden with
  | union a b iha ihb | inter a b iha ihb =>
      have missing : fresh ∉ outerLabels a ∧ fresh ∉ outerLabels b := by
        simpa only [outerLabels, List.mem_append, not_or] using unused
      first
      | exact and_congr (iha hidden member missing.1) (ihb hidden member missing.2)
      | exact or_congr (iha hidden member missing.1) (ihb hidden member missing.2)
  | record current payload tail ihp iht | recordDefault current tail payload iht ihp =>
      have missing : fresh ≠ current ∧ fresh ∉ outerLabels tail := by
        simpa only [outerLabels, List.mem_cons, not_or] using unused
      have removed : ¬ (query = current ∧ current ∉ hidden) := by
        rintro ⟨rfl, visible⟩
        exact visible member
      simpa [ProbeStep, MaskedProbeStep, removed, missing.1] using iht hidden member missing.2
  | mask more type ih =>
      have missing : fresh ∉ more ∧ fresh ∉ outerLabels type := by
        simpa only [outerLabels, List.mem_append, not_or] using unused
      have inner := ih (hidden ++ more) (List.mem_append.mpr (Or.inl member)) missing.2
      have erase := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) type fresh .impossible more []
        (by simp [missing.1])).1
      exact inner.trans erase.symm
  | nil | cons | inl | inr => trivial
  | _ => simp [ProbeStep, MaskedProbeStep]

def Observation.isOuterField : Observation Row → Prop
  | .field _ _ | .optional _ _ => True
  | _ => False

/-- Only root field observations inspect an outer mask. Payload paths,
negative arguments and both effect rows retain their original observations. -/
theorem maskedProbeStep_other (type : Ty Row) (first last : List Nat)
    (obs : Observation Row) (other : ¬ obs.isOuterField) :
    MaskedProbeStep leRow env argumentOrder first type obs ↔
      MaskedProbeStep leRow env argumentOrder last type obs := by
  induction type using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing first last obs with
  | union a b iha ihb =>
      cases obs <;> try rfl
      all_goals exact and_congr (iha first last _ other) (ihb first last _ other)
  | inter a b iha ihb =>
      cases obs <;> try rfl
      all_goals exact or_congr (iha first last _ other) (ihb first last _ other)
  | mask hidden type ih =>
      cases obs <;> try rfl
      all_goals exact ih (first ++ hidden) (last ++ hidden) _ other
  | nil | cons | inl | inr => trivial
  | _ =>
      cases obs <;> try rfl
      all_goals exact False.elim (other trivial)

/-- Pointwise mask monotonicity, with arbitrary negative-argument semantics.
The proof chooses one fresh root label for both compared finite types. -/
theorem maskedProbeStep_mono (source target : Ty Row)
    (below : ∀ obs, ProbeStep leRow env argumentOrder target obs →
      ProbeStep leRow env argumentOrder source obs)
    (hidden : List Nat) (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden target obs →
      MaskedProbeStep leRow env argumentOrder hidden source obs := by
  let fresh := freshLabel (outerLabels source ++ outerLabels target)
  have missing := fresh_not_mem (outerLabels source ++ outerLabels target)
  have freshSource : fresh ∉ outerLabels source := fun member =>
    missing (List.mem_append.mpr (Or.inl member))
  have freshTarget : fresh ∉ outerLabels target := fun member =>
    missing (List.mem_append.mpr (Or.inr member))
  cases obs with
  | field label payload =>
      by_cases member : label ∈ hidden
      · intro accepted
        exact (maskedProbeStep_hidden_field source label fresh hidden member freshSource payload).mpr
          (below _ ((maskedProbeStep_hidden_field target label fresh hidden member freshTarget payload).mp accepted))
      · intro accepted
        have sourceSame := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) source label payload hidden [] (by simp [member])).1
        have targetSame := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) target label payload hidden [] (by simp [member])).1
        exact sourceSame.mpr (below _ (targetSame.mp accepted))
  | optional label payload =>
      by_cases trivialPayload : payload = .trivial
      · subst payload
        intro accepted
        have known := (maskedProbeStep_optional_trivial hidden target label).mp accepted
        have unmasked := (maskedProbeStep_other target hidden [] .records (by simp [Observation.isOuterField])).mp known
        have result := (maskedProbeStep_other source hidden [] .records (by simp [Observation.isOuterField])).mpr (below _ unmasked)
        exact (maskedProbeStep_optional_trivial hidden source label).mpr result
      · by_cases member : label ∈ hidden
        · intro accepted
          exact (maskedProbeStep_hidden_query source label fresh hidden member freshSource payload trivialPayload).2.mpr
            (below _ ((maskedProbeStep_hidden_query target label fresh hidden member freshTarget payload trivialPayload).2.mp accepted))
        · intro accepted
          have sourceSame := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) source label payload hidden [] (by simp [member])).2
          have targetSame := (maskedProbeStep_query_congr (leRow := leRow) (env := env) (argumentOrder := argumentOrder) target label payload hidden [] (by simp [member])).2
          exact sourceSame.mpr (below _ (targetSame.mp accepted))
  | _ =>
      intro accepted
      exact (maskedProbeStep_other source hidden [] _ (by simp [Observation.isOuterField])).mpr
        (below _ ((maskedProbeStep_other target hidden [] _ (by simp [Observation.isOuterField])).mp accepted))

/-- Every finite mask preserves producer subtyping, including arbitrary
parameter assignments in negative arrow observations. -/
theorem producerLe_mask (hidden : List Nat) {source target : Ty Row}
    (below : ProducerLe leRow source target) :
    ProducerLe leRow (.mask hidden source) (.mask hidden target) := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  rw [probeAt_mask] at accepted ⊢
  have finite := (producerLe_iff_probe _ _).mp below rank env
  cases rank <;> exact maskedProbeStep_mono source target finite hidden obs accepted

theorem producerEq_mask (hidden : List Nat) {source target : Ty Row}
    (same : ProducerEq leRow source target) :
    ProducerEq leRow (.mask hidden source) (.mask hidden target) :=
  ⟨producerLe_mask hidden same.1, producerLe_mask hidden same.2⟩

end Yulang.CommonNominalFullDemand
