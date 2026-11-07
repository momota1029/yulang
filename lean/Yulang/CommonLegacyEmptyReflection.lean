import Yulang.CommonLegacyTyping
import Yulang.CoreContextualSourceInference

/-!
# Reflection of exact empty against every legacy result

Exact emptiness and width are different common producers. Nevertheless an
arbitrary embedded legacy result imposes the same upper-bound condition on
both: old observations cannot express the newly added absence information.
The proof retains all finite depths, negative ranks, row annotations and
regular legacy targets. It does not identify exact emptiness with width.

This closes the changed empty-record typing rule at the legacy-result
boundary. General source reflection still has to recover shared legacy
witnesses from arbitrary common existential witnesses; that obligation is
not asserted by the empty-expression theorem here.
-/

namespace Yulang.CommonLegacyEmptyReflection

open Inference
open CommonFiniteEmbedding (embedOld embedObservation embedEnvironment NewCompare OldCompare)

universe u
variable {Row : Type u}

theorem probe_embedded (leRow : Row → Row → Prop) (rank : Nat)
    (environment : ProducerContextual.Environment Row) (type : StructuralBase.Ty Row)
    (observation : ProducerContextual.Observation Row) :
    CommonFinite.ProbeAt leRow rank (embedEnvironment environment) (embedOld type)
        (embedObservation observation) ↔
      ProducerContextual.ProbeAt leRow rank environment type observation := by
  cases rank with
  | zero =>
      simpa only [CommonFinite.ProbeAt, ProducerContextual.ProbeAt,
        CommonFiniteEmbedding.project_embed_observation] using
        CommonFiniteEmbedding.probeStep_embed_project (leRow := leRow) (embedEnvironment environment) environment
          (fun _ _ => True) (fun _ _ => True) rfl type (fun _ _ _ => Iff.rfl) (embedObservation observation)
  | succ rank =>
      change CommonFinite.ProbeStep leRow (embedEnvironment environment) (NewCompare leRow rank)
        (embedOld type) (embedObservation observation) ↔
          ProducerContextual.ProbeStep leRow environment (OldCompare leRow rank) type observation
      simpa only [CommonFiniteEmbedding.project_embed_observation] using
        CommonFiniteEmbedding.probeStep_embed_project (leRow := leRow) (embedEnvironment environment) environment
          (NewCompare leRow rank) (OldCompare leRow rank) rfl type
          (fun name domain _ => CommonFiniteEmbedding.comparison_embedding_exact leRow rank
            (environment.types name) domain) (embedObservation observation)

/-- On every embedded old observation, exact empty has the old width
record's response, for arbitrary old environments and every negative rank. -/
theorem exact_empty_old_probe (leRow : Row → Row → Prop) (rank : Nat)
    (environment : ProducerContextual.Environment Row) (observation : ProducerContextual.Observation Row) :
    CommonFinite.ProbeAt leRow rank (embedEnvironment environment) .exactEmpty (embedObservation observation) ↔
      ProducerContextual.ProbeAt leRow rank environment .emptyRecord observation := by
  cases rank <;> cases observation <;> rfl

theorem finite_exact_empty_upper_old_iff (leRow : Row → Row → Prop) (target : StructuralBase.Ty Row) :
    CommonFinite.ProducerLe leRow .exactEmpty (embedOld target) ↔
      CommonFinite.ProducerLe leRow .emptyRecord (embedOld target) := by
  constructor
  · intro below
    apply (CommonFiniteEmbedding.contextual_embedding_exact leRow .emptyRecord target).mpr
    apply (ProducerContextual.producerLe_iff_probe _ _).mpr
    intro rank environment observation accepted
    apply (exact_empty_old_probe leRow rank environment observation).mp
    exact (CommonFinite.producerLe_iff_probe _ _).mp below rank (embedEnvironment environment)
      (embedObservation observation) ((probe_embedded leRow rank environment target observation).mpr accepted)
  · intro below
    exact CommonFinite.producerLe_trans CommonFinite.exactEmpty_below_width below

/-- Arbitrary old regular targets, including open parameter graphs and
negative arrow positions. The result remains an upper-bound equivalence;
the two common source types are not equated. -/
theorem exact_empty_upper_old_iff (target : RegularInferenceModel.Ty Common.Row) :
    Common.Subtype Common.exactEmpty (Common.embedOld target) ↔
      Common.Subtype Common.emptyRecord (Common.embedOld target) := by
  constructor
  · intro below depth
    have observed := below depth
    rw [Common.embedOld_observe_exact] at observed ⊢
    exact (finite_exact_empty_upper_old_iff Common.rowLe _).mp observed
  · intro below depth
    have observed := below depth
    rw [Common.embedOld_observe_exact] at observed ⊢
    exact (finite_exact_empty_upper_old_iff Common.rowLe _).mpr observed

theorem exact_empty_upper_contextual_iff (target : RegularInferenceModel.Ty Common.Row) :
    Common.Subtype Common.exactEmpty (Common.embedOld target) ↔
      ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Common.Row) Common.rowLe
        .emptyRecord target :=
  (exact_empty_upper_old_iff target).trans (Common.contextual_embedding_exact .emptyRecord target)

abbrev legacyModel := SourcePrincipalInference.model Common.rowAlgebra
abbrev contextualModel := ContextualSourcePrincipalInference.model Common.rowAlgebra

/-- The changed source rule reflects at every old result type and every
result row. No source-support or successful-inference premise is needed. -/
theorem empty_record_typing_exact (target : Comp legacyModel) :
    Core.PresenceGeneration.Typing Common.model [] .emptyRecord (Common.embedComp target) ↔
      Inference.Typing contextualModel [] .emptyRecord target := by
  constructor
  · intro typed
    cases typed with
    | emptyRecord bounded =>
        exact .emptyRecord ⟨(exact_empty_upper_contextual_iff target.1).mp bounded.1, bounded.2⟩
  · intro typed
    cases typed with
    | emptyRecord bounded =>
        exact .emptyRecord ⟨(exact_empty_upper_contextual_iff target.1).mpr bounded.1, bounded.2⟩

/-- The final legacy-instance readback once contextual old-carrier typing
has been obtained. It keeps the exact requested row and compares embedded
values by the common independent demand equivalence. -/
theorem contextual_typing_legacy_reflected (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true) (target : Comp legacyModel)
    (typed : Inference.Typing contextualModel [] expression target) :
    ∃ old : Comp legacyModel,
      (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra old ∧
        Common.Equivalent (Common.embedOld target.1) (Common.embedOld old.1) ∧ target.2 = old.2 := by
  have contextualInstance := (Core.ContextualRequiredInference.legacy_source_typing_exact
    Common.rowAlgebra Common.rowLe_antisymm expression supported target).mpr typed
  obtain ⟨oldValue, accepted, equivalent⟩ := Core.ProducerContextualInstances.legacy_instances_reflected
    Common.rowAlgebra (SourcePrincipalInference.infer expression) target contextualInstance
  exact ⟨(oldValue, target.2), accepted,
    Common.equivalent_symm ((Common.contextual_equivalence_exact oldValue target.1).mpr equivalent), rfl⟩

theorem empty_record_legacy_instances_reflected (target : Comp legacyModel)
    (typed : Core.PresenceGeneration.Typing Common.model [] .emptyRecord (Common.embedComp target)) :
    ∃ old : Comp legacyModel,
      (SourcePrincipalInference.infer .emptyRecord).Instance Common.rowAlgebra old ∧
        Common.Equivalent (Common.embedOld target.1) (Common.embedOld old.1) ∧ target.2 = old.2 :=
  contextual_typing_legacy_reflected .emptyRecord
    (SourcePrincipalInference.recordFree_supported .emptyRecord trivial) target
    ((empty_record_typing_exact target).mp typed)

end Yulang.CommonLegacyEmptyReflection
