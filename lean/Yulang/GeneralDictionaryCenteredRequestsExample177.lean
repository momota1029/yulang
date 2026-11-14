import Yulang.GeneralDictionaryCenteredScalarRequests177
import Yulang.GeneralDictionaryObservedClosedExample
import Yulang.GeneralDictionaryObservedInitialExample

/-! An inhabited empty-journal candidate with a nonempty named nominal output.
The actual requests have a closed source tree. Ground-boundary reachability and
installation are not asserted by this model-indexed regression. -/
namespace Yulang.GeneralDictionaryCenteredRequestsExample177
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)
open GeneralDictionaryObservedInitialExample (source context source_models)
open GeneralNominalExamples (model interpretation)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps

abbrev request := GeneralDictionaryObservedClosedExample.request
abbrev equation : Equation := ⟨0,0,request.pattern⟩
abbrev declaration : Declaration := ⟨179,1,[.app 2 []],[],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev root : Occurrence roles := ⟨179,⟨1,fun _ => (1,1),[⟨0,0⟩],by
  intro o member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev start := initial context root

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro e member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals intro c member; cases member

theorem requests_exact (captures : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests source registry root declaration checked captures = [request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro c member; cases member)]
  rfl

theorem observed : GeneralDictionaryObservedClosedRequests.Observed source interpretation [request] :=
  GeneralDictionaryObservedClosedExample.observed

theorem report_exact : report context declaration [(1,1)] =
    { inspected := [(1,1)],checked := [(1,1),(1,1)] } := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,inspectMany,inspect,Report.visit,Report.append]

theorem branch : BranchModels registry context root declaration checked [(1,1)] model := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_models,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]
  · unfold generated
    rw [requests_exact]
    exact GeneralDictionaryObservedClosedRequests.generated_models source interpretation [request] observed _ _ _ model source_models

theorem ready : RequestReady registry context root declaration checked [(1,1)] := by
  constructor
  · intro output member; cases List.mem_singleton.mp member
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  · unfold generated
    rw [requests_exact]
    exact (GeneralDictionaryObservedClosedRequests.generated_shape source interpretation [request] observed).2

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite source.seed root,rfl⟩

theorem prepared : Prepared registry context root declaration checked := by
  refine ⟨?_,?_,?_,[(1,1)],by decide +kernel,?_,ready,model,branch⟩
  · exact GeneralDictionaryObservedInitialExample.metadata
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases List.mem_singleton.mp member
      simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro key _ present
    have below : GeneralNominalAllocation.source source registry root.identity key ≤ source.seed := by
      simp [GeneralNominalState.sources,List.ofFn_succ] at present
      rcases present with h | h | h | h <;> rw [h] <;> decide +kernel
    exact False.elim (GeneralNominalAllocation.source_initial_fresh source registry root.identity key _ below rfl)
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,by simp [start,initial,initialAt,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial,rootSite],by simp [start,initial,initialAt],by simp,rfl,
    by decide +kernel,prepared,model,branch⟩
  exact GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked rfl _

theorem actual_observed : GeneralDictionaryObservedClosedRequests.Observed packet.context.state
    packet.context.interpretation (GeneralNominalMaterialization.requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings) := by
  change GeneralDictionaryObservedClosedRequests.Observed source interpretation
    (GeneralNominalMaterialization.requests source registry root declaration checked packet.bindings)
  rw [requests_exact]; exact observed

theorem inhabited : Models start model :=
  (point_initial_models context root (fun _ => rfl) model).mpr source_models

theorem evidence : GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) := by
  apply GeneralDictionaryCenteredScalarRequests177.candidate_evidence candidate [.int] rfl _ actual_observed model inhabited [] .nil
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

theorem regression : Models start model ∧ start.plans = [] ∧ start.erased.current.packets = [] ∧
    root.demand.outputs ≠ [] ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  ⟨inhabited,rfl,rfl,(by intro h; cases h),evidence⟩

abbrev missingTarget : GeneralNominalMaterialization.Request := { request with target := 2 }

theorem missing_target_rejected :
    ¬ GeneralDictionaryObservedClosedRequests.Observed source interpretation [missingTarget] := by
  intro observedBad
  obtain ⟨slot,equal,_⟩ := observedBad missingTarget (List.mem_singleton_self _)
  have below := slot.isLt
  change slot.val < 2 at below
  change 2 = slot.val at equal
  omega

abbrev wrongTarget : GeneralNominalMaterialization.Request := { request with target := 1 }

theorem wrong_target_rejected :
    ¬ GeneralDictionaryObservedClosedRequests.Observed source interpretation [wrongTarget] := by
  intro observedBad
  obtain ⟨slot,equal,⟨tree⟩⟩ := observedBad wrongTarget (List.mem_singleton_self _)
  have same : slot = 1 := Fin.ext equal.symm
  subst slot
  have tree : GeneralDictionaryObservedClosedRequests.Tree source 1 (.nominal 0 [.scalar .int]) := by
    simpa [GeneralNominalInspection.translate,normalize,normalizeArgs,interpretation,wrongTarget,request,
      GeneralDictionaryObservedClosedExample.request] using tree
  have scalarOnly : ∀ {q}, GeneralDictionaryObservedClosedRequests.Tree source 1 q →
      ∃ base, q = .scalar base := by
    intro q witness
    cases witness <;> simp_all [source,GeneralNominalExamples.state]
  obtain ⟨base,impossible⟩ := scalarOnly tree
  cases impossible

end Yulang.GeneralDictionaryCenteredRequestsExample177
