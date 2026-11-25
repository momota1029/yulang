import Yulang.GeneralDeclarativeI65I74StructuralWhereEmbed428
import Yulang.GeneralDeclarativeI65I72FiniteSupport402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open I72 (OutputNeed ExactOutputSupport SupportForest SourcePrimitives SourceTrace Event)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Summarizes)

noncomputable def transportOriginalSupport428 {A B : SourcePrimitives}
    (rule : NamedRuleMap428 A B) {s : I72.State} {needs : List (OutputNeed s)}
    (forest : SupportForest A s needs) : SupportForest B s needs :=
  match forest with
  | .nil => .nil
  | .cons producer completed receipt tail =>
    .cons (mapNamedTrace428 rule producer).val completed receipt (transportOriginalSupport428 rule tail)

noncomputable def transportSelectedProducer428 {A B : SourcePrimitives}
    (rule : NamedRuleMap428 A B) {s : I72.State} {need : OutputNeed s}
    (actual : ExactOutputSupport A s need) : ExactOutputSupport B s need :=
  ⟨actual.event,actual.diagnostic,(mapNamedTrace428 rule actual.source).val,
    actual.completion,actual.sameTypedOutput⟩

/-- The commuting square is at each concrete ordinal of an already
given original support forest. It preserves the exact event object
and the entire original typed receipt proof, not just the key, value,
output target or length of the support journal. -/
theorem lookup_after_rule_inclusion_is_the_same_original_producer428
    {A B : SourcePrimitives} (rule : NamedRuleMap428 A B) {s : I72.State}
    {needs : List (OutputNeed s)} (before : SupportForest A s needs)
    (i : Nat) {need : OutputNeed s} (atIndex : needs[i]? = some need) :
    (transportOriginalSupport428 rule before).atOriginal i atIndex =
      transportSelectedProducer428 rule (before.atOriginal i atIndex) := by
  cases before with
  | nil => simp at atIndex
  | cons prior done got tail =>
    cases i with
    | zero =>
      have eq := Option.some.inj atIndex
      subst need
      rfl
    | succ i =>
      exact lookup_after_rule_inclusion_is_the_same_original_producer428 rule tail i (by simpa using atIndex)
termination_by i

theorem old_support_at_original_position_keeps_event_and_receipt428
    {A B : SourcePrimitives} (rule : NamedRuleMap428 A B) {s : I72.State}
    {needs : List (OutputNeed s)} (before : SupportForest A s needs)
    (i : Nat) {need : OutputNeed s} (atIndex : needs[i]? = some need) :
    let original := before.atOriginal i atIndex
    let later := (transportOriginalSupport428 rule before).atOriginal i atIndex
    later.event = original.event ∧ later.diagnostic = original.diagnostic ∧
      namedTraceNeeds428 later.source = namedTraceNeeds428 original.source ∧
      namedTraceWrites428 later.source = namedTraceWrites428 original.source := by
  dsimp only
  rw [lookup_after_rule_inclusion_is_the_same_original_producer428]
  exact ⟨rfl,rfl,(mapNamedTrace428 rule (before.atOriginal i atIndex).source).property.2,
    (mapNamedTrace428 rule (before.atOriginal i atIndex).source).property.1⟩

private theorem current_named_selected_event_owns_its_fixed_targets428
    {s q t} {e : Event s q} (source : SourceTrace I72.RepeatedCenters421.R13 s q t (some e))
    (m : I72.Model) (fit : I72.Fits s m) : I72.FixedTargets m e := by
  cases source with
  | selected _ _ picked _ _ =>
    exact (current_R13_local_law_for_mixed_named_traces428 picked m fit).2

/-- An original legacy support entry remains the exact producer at
the actual original index after rule inclusion. Its semantic receipt
comes from the original selected event, not from the new rule or a
second fit. This does not assert new producers or model soundness
of arbitrary rules in the destination system. -/
theorem transported_existing_support_keeps_literal_output_and_same_model428
    {B : SourcePrimitives} (rule : NamedRuleMap428 I72.RepeatedCenters421.R13 B)
    {s : I72.State} {needs : List (OutputNeed s)}
    (before : SupportForest I72.RepeatedCenters421.R13 s needs)
    (i : Nat) {need : OutputNeed s} (atIndex : needs[i]? = some need) :
    let prior := before.atOriginal i atIndex
    let attached := (transportOriginalSupport428 rule before).atOriginal i atIndex
    attached.event = prior.event ∧
      need.expected.occurrence = need.producer.occurrence ∧
      need.expected.outputOrdinal = need.ordinal.val ∧
      need.expected.original = need.producer.demand.outputs[need.ordinal] ∧
      ∀ m : I72.Model, I72.Fits s m → I72.DictionaryEvidence s m need.producer need.dictionary ∧
        ∃ ty, need.expected.actualEquation m = some (need.producer.demand.outputs[need.ordinal].target, ty) ∧
          Equivalent (m.assignment need.producer.demand.outputs[need.ordinal].target).1 ty := by
  dsimp only
  rw [lookup_after_rule_inclusion_is_the_same_original_producer428]
  let old := before.atOriginal i atIndex
  have addr := congrArg NamedMixedReceipt401.occurrence old.sameTypedOutput.symm
  have order := congrArg NamedMixedReceipt401.outputOrdinal old.sameTypedOutput.symm
  have literal := congrArg NamedMixedReceipt401.original old.sameTypedOutput.symm
  refine ⟨rfl,addr,order,literal,fun m fit => ?_⟩
  refine ⟨actual_named_trace_same_model_dictionary428 current_R13_local_law_for_mixed_named_traces428
    old.source m fit _ old.completion,?_⟩
  obtain ⟨ty,read,holds⟩ := current_named_selected_event_owns_its_fixed_targets428 old.source m fit need.ordinal
  rw [old.sameTypedOutput] at read
  exact ⟨ty,read,holds⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere428
