import Yulang.GeneralDictionaryCapturedScalarRefresh

/-! Full current-model scalar entailment does not alone justify an I26 head.
This bridge states the additional independent trusted-slice alias premise
explicitly. It does not prove that premise or discharge the captured consumer. -/
noncomputable section
namespace Yulang.GeneralDictionaryCapturedTrustedBoundary
open GeneralNominalSupport GeneralNominalSharedSupport
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedProducer
open GeneralDictionaryCapturedScalarRefresh CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

/-- Producer output semantics alone determine its allocated target. -/
theorem producer_output_int (m : GeneralNominalCommonBridge.Assignment)
    (outputs : GeneralNominalPacketSupport.Outputs candidate m) :
    Equivalent (m target).1 (.base .int) := by
  have member : (.source target,GeneralNominalRecursiveInspection.Test.scalar .int) ∈
      (GeneralNominalPacketSupport.namedSchema candidate).tests := by
    rw [schema_exact]; exact List.mem_singleton_self _
  exact (outputs.1 _ member).2 _ (.source target)

/-- An independently justified alias, not an unrestricted journal consequence,
can carry a settled/trusted producer result back to the captured source. -/
theorem ready_from_trusted_alias (state : Tracked roles)
    (context : state.current.context = scalarContext)
    (facts : List (Fact roles)) (readbacks : Readbacks)
    (trusted : Trusted state facts readbacks)
    (support : List (GeneralSourceDictionaries.Occurrence roles))
    (output : Fact.outputs candidate support ∈ facts)
    (alias : ∀ m, GeneralNominalSharedSupport.Models state facts m →
      Equivalent (m target).1 (m 2).1) :
    GeneralNominalSharedSupport.ReadyAt state 2 := by
  let observation := GeneralCanonicalObservations.Observation.normalized scalarBase (2 : Fin 5) (.base .int)
  have head : GeneralNominalSupport.Head scalarState 2 (.scalar .int) observation :=
    .scalar (snapshot := scalarState) 2 .int rfl
  refine ⟨.scalar .int,observation,?_,facts,readbacks,trusted,scalarState,observation,head,?_⟩
  · rw [context]; exact head
  · intro m valid
    have scalar := producer_output_int m (valid.2 _ output)
    have same := alias m valid
    exact ⟨subtype_trans same.2 scalar.1,subtype_trans scalar.2 same.1⟩

/-- Parent outputs would supply the missing alias, but putting this fact in a
trusted explanation is a separate obligation; parent settlement is not assumed. -/
theorem alias_from_parent_output (state : Tracked roles) (facts : List (Fact roles))
    (support : List (GeneralSourceDictionaries.Occurrence roles))
    (output : Fact.outputs packet support ∈ facts)
    (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSharedSupport.Models state facts m) :
    Equivalent (m target).1 (m 2).1 :=
  output_equals_captured m (valid.2 _ output)

/-- Using parent settlement to justify this consumer would already require the
consumer's discharge. This is a dependency fact, not an impossibility theorem. -/
theorem parent_settlement_requires_consumer
    (state : GeneralNominalSaturationState.State roles)
    (settled : GeneralNominalSettledSupport.PacketSettled state packet) :
    GeneralNominalSupport.Discharged state consumer := by
  apply settled.2 consumer
  rw [GeneralDictionarySharedCapturedInstallation.children]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

end Yulang.GeneralDictionaryCapturedTrustedBoundary
