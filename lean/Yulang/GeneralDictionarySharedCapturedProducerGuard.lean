import Yulang.GeneralDictionarySharedCapturedProducer
import Yulang.GeneralDictionarySharedCapturedInputReady
namespace Yulang.GeneralDictionarySharedCapturedProducerGuard
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveInspection
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedRefresh GeneralDictionarySharedCapturedProducer
open GeneralDeclarationExamples (roles)

 theorem input_member : GeneralDictionarySharedCapturedInputReady.input ∈ refreshed.facts := by
  change _ ∈ GeneralDictionarySharedCapturedInstallation.after.facts
  rw [GeneralDictionarySharedCapturedInputReady.facts]
  exact List.mem_cons_self

theorem endpoint_ready (slot : Fin 5) (which : slot = 3 ∨ slot = 4) :
    ReadyAt refreshed [] (base.source slot) := by
  have desc : snapshot.nominals slot = some lastDescriptor := by
    rcases which with rfl | rfl <;> rfl
  have head : Head snapshot (base.source slot) (.nominal 0 1)
      (.nominal base slot lastDescriptor) := Head.nominal (snapshot := snapshot) slot lastDescriptor desc
  refine ⟨.nominal 0 1,_,head,snapshot,_,head,?_⟩
  intro assignment valid
  have inputs := valid.2 _ input_member (by intro p h; cases h)
  change GeneralNominalState.Denotes base assignment slot lastDescriptor
  apply (GeneralNominalState.denotes_singleton_exact base assignment slot 2 lastDescriptor rfl).mpr
  exact GeneralDictionarySharedCapturedInputReady.input_endpoint_equation assignment inputs _
    (by rcases which with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl)

theorem only (d : Declaration) (visible : d ∈ registry.declarations)
    (role : d.role = producer.demand.role) : d = declaration := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · cases role
  · rfl

theorem reads_exact : readsMany snapshot
    (GeneralNominalInspection.queries snapshot context.interpretation declaration) [(3,4)] = [3,4] := by
  rw [GeneralDictionarySharedCapturedProducer.queries]
  rw [readsMany.eq_def]
  have empty : readsMany snapshot [] [] = [] := by rw [readsMany.eq_def]
  dsimp only
  rw [empty,List.append_nil,reads.eq_def]
  change 3 :: 4 :: (readsMany snapshot [.variables [0]] [(2,2)] ++
    readsMany snapshot [.variables [0]] [(2,2)]) = _
  simp [readsMany,reads]

theorem decisions : DecisionGuard refreshed registry producer [] := by
  refine ⟨(by intro _ h; cases h),?_,?_⟩
  · intro i
    rw [GeneralDictionarySharedCapturedInstallation.producer_inputs]
    exact endpoint_ready 3 (Or.inl rfl)
  · intro d visible role intervals located slot member
    have eq := only d visible role
    subst d
    have eq := Option.some.inj (bounds.symm.trans located)
    subst intervals
    change slot ∈ readsMany snapshot
      (GeneralNominalInspection.queries snapshot context.interpretation declaration) [(3,4)] at member
    rw [reads_exact] at member
    rcases List.mem_cons.mp member with a | b
    · subst slot; exact endpoint_ready 3 (Or.inl rfl)
    · have eq := List.mem_singleton.mp b
      subst slot; exact endpoint_ready 4 (Or.inr rfl)

theorem shared_decisions : GeneralNominalSharedSupport.DecisionGuard registry refreshed producer := by
  refine ⟨?_,?_⟩
  · intro i
    rw [GeneralDictionarySharedCapturedInstallation.producer_inputs]
    exact GeneralDictionarySharedCapturedInputReady.lo_ready
  · intro d visible role intervals located slot member
    have eq := only d visible role
    subst d
    have eq := Option.some.inj (bounds.symm.trans located)
    subst intervals
    change slot ∈ readsMany snapshot
      (GeneralNominalInspection.queries snapshot context.interpretation declaration) [(3,4)] at member
    rw [reads_exact] at member
    rcases List.mem_cons.mp member with a | b
    · subst slot; exact GeneralDictionarySharedCapturedInputReady.lo_ready
    · have eq := List.mem_singleton.mp b
      subst slot; exact GeneralDictionarySharedCapturedInputReady.hi_ready

theorem coherent : GeneralNominalSharedCaptures.InputCoherence candidate := by
  apply GeneralNominalSharedCaptures.empty_input_coherent
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

theorem guard : GeneralNominalSharedSteps.PacketGuard refreshed candidate [] := by
  apply GeneralNominalSharedSteps.leaf_guard rfl coherent
  · apply GeneralNominalValueSupport.source_packet
    exact ⟨⟨decisions.1,decisions.2.1,
      decisions.2.2 declaration (by simp) rfl candidate.bounds bounds⟩,decisions⟩
  · exact shared_decisions
end Yulang.GeneralDictionarySharedCapturedProducerGuard
