import Yulang.CommonLegacyEmptyReflection
import Yulang.CommonPresence

/-!
# Constructor-aware comparison at every legacy upper boundary

Agreement here compares responses to embedded old observations, at every
constructor depth and every negative rank. It does not identify exact empty
with width, or erase arbitrary common types by a global function.

The relation is closed under positive constructors, including first-field-wins
record tails. Consequently, a whole constructor value can be reflected against
an arbitrary old regular target at once; its children are not independently
rounded to a finite envelope. This is a structural witness lemma, not the
remaining mixed-variance existential recovery theorem for every source.
-/

namespace Yulang.CommonLegacyWitnessPositive

open CommonFiniteEmbedding (embedObservation embedEnvironment)

universe u
variable {Row : Type u}

def FiniteAgrees (leRow : Row → Row → Prop)
    (source : CommonFinite.Ty Row) (legacy : StructuralBase.Ty Row) : Prop :=
  ∀ rank environment observation,
    CommonFinite.ProbeAt leRow rank (embedEnvironment environment) source
        (embedObservation observation) ↔
      ProducerContextual.ProbeAt leRow rank environment legacy observation

namespace FiniteAgrees

theorem embedded (leRow : Row → Row → Prop) (legacy : StructuralBase.Ty Row) :
    FiniteAgrees leRow (CommonFiniteEmbedding.embedOld legacy) legacy :=
  fun rank environment observation =>
    CommonLegacyEmptyReflection.probe_embedded leRow rank environment legacy observation

theorem exactEmpty (leRow : Row → Row → Prop) :
    FiniteAgrees leRow .exactEmpty .emptyRecord :=
  CommonLegacyEmptyReflection.exact_empty_old_probe leRow

theorem union {leRow : Row → Row → Prop}
    {first last : CommonFinite.Ty Row} {oldFirst oldLast : StructuralBase.Ty Row}
    (left : FiniteAgrees leRow first oldFirst) (right : FiniteAgrees leRow last oldLast) :
    FiniteAgrees leRow (.union first last) (.union oldFirst oldLast) := by
  intro rank environment observation
  simpa only [CommonFinite.probeAt_union, ProducerContextual.probeAt_union] using
    and_congr (left rank environment observation) (right rank environment observation)

theorem inter {leRow : Row → Row → Prop}
    {first last : CommonFinite.Ty Row} {oldFirst oldLast : StructuralBase.Ty Row}
    (left : FiniteAgrees leRow first oldFirst) (right : FiniteAgrees leRow last oldLast) :
    FiniteAgrees leRow (.inter first last) (.inter oldFirst oldLast) := by
  intro rank environment observation
  simpa only [CommonFinite.probeAt_inter, ProducerContextual.probeAt_inter] using
    or_congr (left rank environment observation) (right rank environment observation)

theorem pair {leRow : Row → Row → Prop}
    {first last : CommonFinite.Ty Row} {oldFirst oldLast : StructuralBase.Ty Row}
    (left : FiniteAgrees leRow first oldFirst) (right : FiniteAgrees leRow last oldLast) :
    FiniteAgrees leRow (.pair first last) (.pair oldFirst oldLast) := by
  intro rank environment observation
  cases observation with
  | pairFirst observation =>
      simpa only [embedObservation, CommonFinite.probeAt_pairFirst,
        ProducerContextual.probeAt_pairFirst] using left rank environment observation
  | pairLast observation =>
      simpa only [embedObservation, CommonFinite.probeAt_pairLast,
        ProducerContextual.probeAt_pairLast] using right rank environment observation
  | _ => cases rank <;> rfl

theorem variant {leRow : Row → Row → Prop} (label : Nat)
    {source : CommonFinite.Ty Row} {legacy : StructuralBase.Ty Row}
    (payload : FiniteAgrees leRow source legacy) :
    FiniteAgrees leRow (.variant label source) (.variant label legacy) := by
  intro rank environment observation
  cases observation with
  | variant expected observation =>
      simpa only [embedObservation, CommonFinite.probeAt_variant,
        ProducerContextual.probeAt_variant] using
        and_congr Iff.rfl (payload rank environment observation)
  | _ => cases rank <;> rfl

theorem record {leRow : Row → Row → Prop} (label : Nat)
    {source rest : CommonFinite.Ty Row} {legacy tail : StructuralBase.Ty Row}
    (payload : FiniteAgrees leRow source legacy) (remaining : FiniteAgrees leRow rest tail) :
    FiniteAgrees leRow (.record label source rest) (.record label legacy tail) := by
  intro rank environment observation
  cases observation with
  | field query observation =>
      by_cases same : query = label
      · subst query
        have payloadAt := payload rank environment observation
        cases rank <;>
          simpa [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep,
            ProducerContextual.ProbeAt, ProducerContextual.ProbeStep, embedObservation,
            List.not_mem_nil] using payloadAt
      · have remainingAt := remaining rank environment (.field query observation)
        cases rank <;>
          simpa only [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep,
            ProducerContextual.ProbeAt, ProducerContextual.ProbeStep, embedObservation,
            same, false_and, ↓reduceIte] using remainingAt
  | _ => cases rank <;> rfl

/-- An arbitrary old domain may occur negatively. Only the new information
in the result is required to agree on old observations. -/
theorem arrow {leRow : Row → Row → Prop} (input : StructuralBase.Ty Row)
    (inputRow outputRow : Row) {source : CommonFinite.Ty Row} {legacy : StructuralBase.Ty Row}
    (output : FiniteAgrees leRow source legacy) :
    FiniteAgrees leRow (.arrow (CommonFiniteEmbedding.embedOld input) inputRow source outputRow)
      (.arrow input inputRow legacy outputRow) := by
  intro rank environment observation
  cases observation with
  | arrowResult observation =>
      have atRank := output rank environment observation
      cases rank <;> exact atRank
  | arrowArgument name =>
      cases rank with
      | zero => rfl
      | succ rank =>
          exact CommonFiniteEmbedding.comparison_embedding_exact leRow rank
            (environment.types name) input
  | _ => cases rank <;> rfl

/-- The old target can contain arbitrary negative arrows, unions, intersections
and rows. Only the source/legacy agreement is used. -/
theorem upper_reflected {leRow : Row → Row → Prop}
    {source : CommonFinite.Ty Row} {legacy : StructuralBase.Ty Row}
    (agreement : FiniteAgrees leRow source legacy) (target : StructuralBase.Ty Row)
    (bounded : CommonFinite.ProducerLe leRow source (CommonFiniteEmbedding.embedOld target)) :
    ProducerContextual.ProducerLe leRow legacy target := by
  apply (ProducerContextual.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  apply (agreement rank environment observation).mp
  exact (CommonFinite.producerLe_iff_probe _ _).mp bounded rank (embedEnvironment environment)
    (embedObservation observation)
    ((CommonLegacyEmptyReflection.probe_embedded leRow rank environment target observation).mpr accepted)

end FiniteAgrees

abbrev OldTy := RegularInferenceModel.Ty Common.Row
abbrev OldLe := ProducerContextualRegular.ProducerLe
  (RegularInferenceModel.graph Common.Row) Common.rowLe

def Agrees (source : Common.Ty) (legacy : OldTy) : Prop :=
  ∀ depth, FiniteAgrees Common.rowLe (Common.observeTy depth source)
    (legacy.eval (RegularValueTypes.observe (RegularInferenceModel.graph Common.Row) depth))

namespace Agrees

theorem embedded (legacy : OldTy) : Agrees (Common.embedOld legacy) legacy := by
  intro depth
  rw [Common.embedOld_observe_exact]
  exact FiniteAgrees.embedded Common.rowLe _

theorem base (scalar : Inference.Base) : Agrees (.base scalar) (.base scalar) :=
  embedded (.base scalar)

theorem exactEmpty : Agrees Common.exactEmpty .emptyRecord :=
  fun _ => FiniteAgrees.exactEmpty Common.rowLe

theorem union {first last : Common.Ty} {oldFirst oldLast : OldTy}
    (left : Agrees first oldFirst) (right : Agrees last oldLast) :
    Agrees (.union first last) (.union oldFirst oldLast) :=
  fun depth => FiniteAgrees.union (left depth) (right depth)

theorem inter {first last : Common.Ty} {oldFirst oldLast : OldTy}
    (left : Agrees first oldFirst) (right : Agrees last oldLast) :
    Agrees (.inter first last) (.inter oldFirst oldLast) :=
  fun depth => FiniteAgrees.inter (left depth) (right depth)

theorem pair {first last : Common.Ty} {oldFirst oldLast : OldTy}
    (left : Agrees first oldFirst) (right : Agrees last oldLast) :
    Agrees (Common.pair first last) (.pair (.node oldFirst) (.node oldLast)) := by
  intro depth
  cases depth with
  | zero =>
      exact FiniteAgrees.pair (FiniteAgrees.embedded Common.rowLe .bottom)
        (FiniteAgrees.embedded Common.rowLe .bottom)
  | succ depth => exact FiniteAgrees.pair (left depth) (right depth)

theorem variant (label : Nat) {source : Common.Ty} {legacy : OldTy}
    (payload : Agrees source legacy) :
    Agrees (Common.variant label source) (.variant label (.node legacy)) := by
  intro depth
  cases depth with
  | zero => exact FiniteAgrees.variant label (FiniteAgrees.embedded Common.rowLe .bottom)
  | succ depth => exact FiniteAgrees.variant label (payload depth)

theorem record (label : Nat) {source rest : Common.Ty} {legacy tail : OldTy}
    (payload : Agrees source legacy) (remaining : Agrees rest tail) :
    Agrees (Common.record label source rest) (.record label (.node legacy) tail) := by
  intro depth
  cases depth with
  | zero => exact FiniteAgrees.record label (FiniteAgrees.embedded Common.rowLe .bottom) (remaining 0)
  | succ depth => exact FiniteAgrees.record label (payload depth) (remaining (depth + 1))

theorem arrow (input : OldTy) (inputRow outputRow : Common.Row)
    {source : Common.Ty} {legacy : OldTy} (output : Agrees source legacy) :
    Agrees (Common.arrow (Common.embedOld input) inputRow source outputRow)
      (.arrow (.node input) inputRow (.node legacy) outputRow) := by
  intro depth
  cases depth with
  | zero =>
      exact FiniteAgrees.arrow .bottom inputRow outputRow
        (FiniteAgrees.embedded Common.rowLe .bottom)
  | succ depth =>
      change FiniteAgrees Common.rowLe
        (.arrow (Common.observeTy depth (Common.embedOld input)) inputRow
          (Common.observeTy depth source) outputRow)
        (.arrow (input.eval (RegularValueTypes.observe (RegularInferenceModel.graph Common.Row) depth))
          inputRow (legacy.eval (RegularValueTypes.observe (RegularInferenceModel.graph Common.Row) depth)) outputRow)
      rw [Common.embedOld_observe_exact]
      exact FiniteAgrees.arrow _ inputRow outputRow (output depth)

/-- Constructor agreement reflects at every old regular upper target, with
all unfolding depths and negative ranks still quantified. -/
theorem upper_reflected {source : Common.Ty} {legacy : OldTy}
    (agreement : Agrees source legacy) (target : OldTy)
    (bounded : Common.Subtype source (Common.embedOld target)) : OldLe legacy target := by
  intro depth
  apply (agreement depth).upper_reflected _
  have observed := bounded depth
  rw [Common.embedOld_observe_exact] at observed
  exact observed

end Agrees

end Yulang.CommonLegacyWitnessPositive
