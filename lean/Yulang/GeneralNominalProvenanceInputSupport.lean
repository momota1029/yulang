import Yulang.GeneralNominalProvenanceObserved
import Yulang.GeneralNominalValueHeadCertificate

/-! The compound inputs emitted by P have empty-support head certificates.
Only ordinary/input facts are used; P's provisional output is not a premise. -/
namespace Yulang.GeneralNominalProvenanceInputSupport
set_option linter.unusedSimpArgs false
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource GeneralNominalProvenancePrefix
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates GeneralNominalSupport
open GeneralNominalSaturationState CommonNominalFullCarrier GeneralDeclarationPatterns GeneralDeclarations

abbrev inputSchema : GeneralNominalMaterialization.Schema :=
  ⟨inputUses 10 0 0 ++ inputUses 11 0 0 ++ inputUses 11 1 1 ++
    inputUses 12 0 1 ++ inputUses 13 0 1 ++ inputUses 13 1 0 ++ inputUses 14 0 0 ++ inputUses 14 1 1,
    inputTests 10 0 ++ inputTests 11 0 ++ inputTests 11 1 ++ inputTests 12 0 ++
    inputTests 13 0 ++ inputTests 13 1 ++ inputTests 14 0 ++ inputTests 14 1,false⟩

theorem input_schema : GeneralNominalPacketSupport.inputSchema packet = inputSchema := by
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  change GeneralNominalMaterialization.generated state interpretation
    ((GeneralDeclarationDemands.emitAll root.identity p p_checked.signature
      (GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings)
      (GeneralNominalAllocation.allocation state registry root.identity p.id)).flatMap
        (fun emission => emission.inputs.flatMap GeneralNominalMaterialization.inputRequests)) = _
  rw [packet_bindings]
  simp [p,extractA,childW,extractB,childG,childP,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,normalizeArgs,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,interpretation,constructors,
    GeneralDeclarationExamples.constructors,GeneralDeclarationDemands.outputTarget,GeneralDeclarationDemands.inputInterval,
    GeneralDeclarationDemands.childDemand,Declaration.outputNames,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.allocation,GeneralNominalAllocation.occurrences,inputSchema,inputUses,inputTests,inputUse,
    argumentLo,argumentHi,allocated,context,state]

theorem materialized_endpoint (assignment : GeneralNominalCommonBridge.Assignment)
    (original : GeneralNominalState.Models state assignment)
    (valid : GeneralNominalPacketSupport.Inputs packet assignment) (target binder : Nat) (names : binder = 0 ∨ binder = 1)
    (entryMember : inputUse target binder ∈ inputSchema.variables)
    (test : (.source target,.nominal 0 1) ∈ inputSchema.tests) :
    Equivalent (assignment target).1 (assignment (if binder = 0 then 1 else 4)).1 := by
  have material := valid.2.2
  change GeneralNominalMaterialization.Models state p _ (report context p pBounds)
    (GeneralNominalPacketSupport.inputSchema packet) assignment at material
  rw [input_schema] at material
  have entry := material.2.1 (inputUse target binder) entryMember
  have fit : ∀ a, Observes assignment (inputUse target binder).origin a →
      GeneralNominalCaptureMerges.Fits assignment (if binder = 0 then (2,2) else (5,5)) a := by
    intro a seen
    have fact := entry.2 a seen
    rcases names with rfl | rfl
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 0) a at fact
      rw [packet_bindings] at fact
      exact fact
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 1) a at fact
      rw [packet_bindings] at fact
      exact fact
  have targetTest : (Test.nominal 0 1).Holds (assignment target).1 :=
    (material.1 (.source target,.nominal 0 1) test).2 _ (.source target)
  rcases names with rfl | rfl
  · apply GeneralNominalMaterializedHeadRecovery.heads_equivalent assignment target 1 0 1 targetTest
    · obtain ⟨arguments,fits,equal⟩ := original.2.1 1 (listDescriptor 2) rfl
      exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length base assignment _ _ fits,equal⟩
    · intro i
      have zero : i.val = 0 := by have bound := i.isLt; omega
      obtain ⟨a,ha⟩ := entry.1
      have bounds := nominal_argument_bounds state assignment original 1 (listDescriptor 2) rfl 0 (2,2) rfl
      obtain ⟨b,hb⟩ := bounds.1
      refine ⟨a,b,?_,?_,?_⟩
      · simpa only [zero,inputUse] using ha
      · have sourceOne : state.base.source (1 : Fin state.base.slots) = 1 := by decide +kernel
        simpa [zero,sourceOne] using hb
      · have one := fit a ha
        have two := bounds.2 b hb
        exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩
  · apply GeneralNominalMaterializedHeadRecovery.heads_equivalent assignment target 4 0 1 targetTest
    · obtain ⟨arguments,fits,equal⟩ := original.2.1 4 (listDescriptor 5) rfl
      exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length base assignment _ _ fits,equal⟩
    · intro i
      have zero : i.val = 0 := by have bound := i.isLt; omega
      obtain ⟨a,ha⟩ := entry.1
      have bounds := nominal_argument_bounds state assignment original 4 (listDescriptor 5) rfl 0 (5,5) rfl
      obtain ⟨b,hb⟩ := bounds.1
      refine ⟨a,b,?_,?_,?_⟩
      · simpa only [zero,inputUse] using ha
      · rw [zero]
        change Observes assignment (.nominal (.source (4 : Fin 8).val) 0 0) b at hb
        have four : (4 : Fin 8).val = 4 := by decide +kernel
        rw [four] at hb
        exact hb
      · have one := fit a ha
        have two := bounds.2 b hb
        exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩

theorem input_fact : Fact.inputs packet [] ∈ afterP.facts := by
  change Fact.inputs packet [] ∈ GeneralNominalSupportChoices.installedFacts start packet ++ []
  rw [GeneralNominalSupportChoices.empty_alternatives start packet rfl source_guard]
  simp

theorem input_head (tracked : Tracked roles) (source : tracked.source = context)
    (retained : Fact.inputs packet [] ∈ tracked.facts) (target binder : Nat)
    (large : 7 < target) (names : binder = 0 ∨ binder = 1)
    (entryMember : inputUse target binder ∈ inputSchema.variables)
    (test : (.source target,.nominal 0 1) ∈ inputSchema.tests) :
    HeadSupported tracked [] target (.nominal 0 1) := by
  apply GeneralNominalValueHeadCertificate.of_nominal_equation tracked [] target
    (if binder = 0 then 2 else 5) 0
  · split <;> omega
  · intro assignment valid
    have original : GeneralNominalState.Models state assignment := by
      have original := valid.1
      rw [source] at original
      exact original
    have material := valid.2 (.inputs packet []) retained (by intro _ impossible; cases impossible)
    have same := materialized_endpoint assignment original material target binder names entryMember test
    rcases names with rfl | rfl
    · have equivalent := (GeneralNominalState.denotes_singleton_exact base assignment 1 2
        (listDescriptor 2) rfl).mp (original.2.1 1 (listDescriptor 2) rfl)
      exact ⟨subtype_trans same.1 equivalent.1,subtype_trans equivalent.2 same.2⟩
    · have equivalent := (GeneralNominalState.denotes_singleton_exact base assignment 4 5
        (listDescriptor 5) rfl).mp (original.2.1 4 (listDescriptor 5) rfl)
      exact ⟨subtype_trans same.1 equivalent.1,subtype_trans equivalent.2 same.2⟩

theorem extract_lower_head : HeadSupported GeneralNominalProvenanceObserved.observed []
    (argumentLo 10 0) (.nominal 0 1) := by
  apply input_head _ rfl input_fact _ 0
  · exact GeneralNominalIdentities.source_above_seed _ _
  · exact Or.inl rfl
  · simp [inputSchema,inputUses]
  · simp [inputSchema,inputTests]

theorem extract_upper_head : HeadSupported GeneralNominalProvenanceObserved.observed []
    (argumentHi 10 0) (.nominal 0 1) := by
  apply input_head _ rfl input_fact _ 0
  · exact GeneralNominalIdentities.source_above_seed _ _
  · exact Or.inl rfl
  · simp [inputSchema,inputUses]
  · simp [inputSchema,inputTests]

theorem extract_lower_ready : ReadyAt GeneralNominalProvenanceObserved.observed [] (argumentLo 10 0) := by
  let observed := GeneralNominalProvenanceObserved.observed
  have current := Head.nominal (snapshot := observed.current.context.state)
    GeneralNominalProvenanceObserved.lowerSlot GeneralNominalProvenanceObserved.currentDescriptor
    GeneralNominalProvenanceObserved.lo_recorded
  rw [GeneralNominalProvenanceObserved.lower_identity] at current
  exact ⟨_,_,current,extract_lower_head⟩

theorem extract_upper_ready : ReadyAt GeneralNominalProvenanceObserved.observed [] (argumentHi 10 0) := by
  let observed := GeneralNominalProvenanceObserved.observed
  have current := Head.nominal (snapshot := observed.current.context.state)
    GeneralNominalProvenanceObserved.upperSlot GeneralNominalProvenanceObserved.currentDescriptor
    GeneralNominalProvenanceObserved.hi_recorded
  rw [GeneralNominalProvenanceObserved.upper_identity] at current
  exact ⟨_,_,current,extract_upper_head⟩

end Yulang.GeneralNominalProvenanceInputSupport
