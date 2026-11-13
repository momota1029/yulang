import Yulang.GeneralDictionaryCapturedInputCountermodel
import Yulang.GeneralDictionarySharedCapturedProducerEvidence
import Yulang.GeneralDictionarySharedTrustTransport

/-! Actual terminal producer output promotion, independent of parent routing. -/
namespace Yulang.GeneralDictionaryCapturedSettledProducerTrust
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveInspection
open GeneralNominalSharedSupport GeneralNominalOriginTerms
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedCapturedRefresh GeneralDictionarySharedCapturedResumption
open GeneralDeclarationExamples (roles)
abbrev parentInput := GeneralDictionarySharedCapturedInputReady.input

theorem parent_trusted : Trusted observed [parentInput] [] :=
  GeneralDictionarySharedTrustTransport.trusted_at scalar_step.choose_spec.2
    (GeneralDictionarySharedTrustTransport.trusted_at producer_step.choose_spec.2
      GeneralDictionarySharedCapturedInputReady.refreshed_trusted)

theorem terminal_settled : GeneralNominalSettledSupport.PacketSettled observed.current candidate := by
  refine ⟨producer_recorded,?_⟩
  intro child member
  rw [GeneralDictionarySharedCapturedProducerEvidence.terminal] at member
  cases member

theorem input_variables_empty : (GeneralNominalPacketSupport.inputSchema candidate).variables = [] := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
    change {declaration with requirements := GeneralCanonicalChildOrder.canonicalRequirements []} = declaration
    simp only [GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  change (GeneralNominalMaterialization.generated snapshot context.interpretation
    ((GeneralCanonicalChildOrder.canonicalEmit producer.identity declaration _ _ _).flatMap
      (fun emission => emission.inputs.flatMap GeneralNominalMaterialization.inputRequests))).variables = []
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [GeneralDeclarationDemands.emitAll,declaration,GeneralDictionaryRecursiveObstruction.declaration,
    GeneralNominalMaterialization.generated]

theorem endpoint_observation (slot : Fin 5) (which : slot = 3 ∨ slot = 4)
    {identity : Nat} {test : Test} {observation : GeneralCanonicalObservations.Observation}
    (head : Head snapshot identity test observation) (equal : identity = base.source slot)
    (m : GeneralNominalCommonBridge.Assignment)
    (inputs : GeneralNominalPacketSupport.Inputs packet m) : observation.Holds m := by
  cases head with
  | scalar other tag recorded => cases recorded
  | structural other kind children recorded => cases recorded
  | nominal other descriptor recorded =>
    have same : other = slot := identifiers_injective equal
    subst other
    have desc : snapshot.nominals slot = some lastDescriptor := by
      rcases which with rfl | rfl <;> rfl
    have same := Option.some.inj (recorded.symm.trans desc)
    subst descriptor
    change GeneralNominalState.Denotes base m slot lastDescriptor
    apply (GeneralNominalState.denotes_singleton_exact base m slot 2 lastDescriptor rfl).mpr
    exact GeneralDictionarySharedCapturedInputReady.input_endpoint_equation m inputs _
      (by rcases which with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl)

theorem input_readback : GeneralNominalSettledSupport.Readback observed [parentInput] candidate := by
  intro slot read test observation head m valid
  change slot ∈ readsMany snapshot
    (GeneralNominalInspection.queries snapshot context.interpretation declaration) [(3,4)] at read
  rw [GeneralDictionarySharedCapturedProducerGuard.reads_exact] at read
  have which : slot = 3 ∨ slot = 4 := by simpa using read
  exact endpoint_observation slot which head rfl m (valid.2 parentInput List.mem_cons_self)

noncomputable def intTerm : Expr Nat := .node (.scalar .int) (fun index => Fin.elim0 index)

theorem int_recipe : Recipe (GeneralNominalPacketSupport.namedSchema candidate) (.source target) intTerm := by
  apply Recipe.node
  · rw [GeneralDictionarySharedCapturedProducer.schema_exact]
    exact List.mem_singleton_self _
  · intro index; exact Fin.elim0 index

noncomputable def certificate (facts : List (Fact roles)) (readbacks : Readbacks) :
    OutputCertificate observed facts readbacks candidate where
  substitution := fun _ => .leaf (.source 0)
  recipes := by
    intro output member
    change output ∈ producer.demand.outputs at member
    rw [producer_output] at member
    cases List.mem_singleton.mp member
    exact ⟨intTerm,int_recipe⟩
  inputs := by
    intro entry member
    rw [GeneralDictionarySharedCapturedProducer.schema_exact] at member
    cases member
  binders := by
    intro entry member
    rw [GeneralDictionarySharedCapturedProducer.schema_exact] at member
    cases member
  uses := by
    intro m valid delta entry member
    rw [GeneralDictionarySharedCapturedProducer.schema_exact] at member
    cases member

theorem producer_output_trusted : ∃ facts readbacks support,
    Trusted observed facts readbacks ∧ Fact.outputs candidate support ∈ facts := by
  obtain ⟨support,alternative⟩ := GeneralNominalSupportChoices.alternatives_exists
    refreshed candidate [] GeneralDictionarySharedCapturedProducerGuard.guard.1.1
  have recorded (fact : Fact roles)
      (member : fact ∈ [Fact.inputs candidate support,Fact.outputs candidate support]) :
      fact ∈ observed.facts := by
    change fact ∈ GeneralNominalSupportChoices.installedFacts refreshed candidate ++ refreshed.facts
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨support,alternative,member⟩
  have inputs : Trusted observed [Fact.inputs candidate support,parentInput] [] :=
    .input candidate support parent_trusted
      (recorded _ List.mem_cons_self) input_readback
      (empty_input_explanation input_variables_empty)
  let cert := certificate [Fact.inputs candidate support,parentInput] []
  have outputs := Trusted.output candidate support cert target intTerm inputs
    (recorded _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) List.mem_cons_self
    terminal_settled int_recipe
  exact ⟨_,_,support,outputs,List.mem_cons_self⟩
end Yulang.GeneralDictionaryCapturedSettledProducerTrust
