import Yulang.GeneralDictionaryVersionedUniversal231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Model-quantified 230 installation regression. InstallationModels records
the old journal plus the actual new merge equations, not an evidence premise.
The operational successor transition and boundary remain separate obligations. -/
namespace Yulang.GeneralDictionaryVersionedCompletion231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedNames231
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def NewMerges (m : Assignment) : Prop :=
  PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalVersionedAllocation231.merges extendedSnapshot registry root.identity declaration newBindings)

def InstallationModels (m : Assignment) : Prop :=
  GeneralNominalCenteredHeadMatStepJournal.Models after m ∧ NewMerges m

theorem compatible (m : Assignment) : GeneralNominalAllocation.Compatible newBindings m := by
  intro first one last two _
  rcases List.mem_cons.mp one with rfl | one
  all_goals first | cases List.mem_singleton.mp one | skip
  all_goals rcases List.mem_cons.mp two with rfl | two
  all_goals first | cases List.mem_singleton.mp two | skip
  all_goals exact subtype_refl _

theorem self_checks (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m
      (GeneralNominalRecursiveInspection.selfChecks extendedSnapshot (GeneralNominalPacketSupport.report currentPacket)) := by
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    (GeneralNominalRecursiveInspection.selfChecks extendedSnapshot
      (GeneralNominalRecursiveCandidates.report extendedContext declaration [(0,0)]))
  rw [GeneralDictionaryUpper230Current.report_exact]
  intro atom member
  simp only [GeneralNominalRecursiveInspection.selfChecks,List.map_cons,List.map_nil,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact subtype_refl _

theorem ordinary (new : NewMerges m) : GeneralNominalVersionedPlans231.Ordinary currentPacket m := by
  unfold GeneralNominalVersionedPlans231.Ordinary
  rw [GeneralDictionaryUpper230Current.bindings_exact]
  exact ⟨compatible m,new,self_checks m⟩

theorem input_fits (valid : InstallationModels m) (name : Nat)
    (needed : name ∈ currentPacket.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed currentPacket name) :
    GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture currentPacket).inputs name)
      (m (GeneralNominalVersionedFrame231.binder currentPlan name)).1 := by
  have same : name = 0 := by
    rcases needed with named | needed
    · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables] using named
    · obtain ⟨clause,member,_⟩ := needed; cases member
  subst name
  rw [GeneralDictionaryVersionedPacket231.binder_exact]
  change GeneralNominalCaptureMerges.Fits m
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ currentPacket.bindings).inputs 0) (m actual).1
  rw [GeneralDictionaryUpper230Current.bindings_exact]
  apply (GeneralNominalVersionedCapture231.capture_interval_exact extendedSnapshot registry root.identity
    declaration newBindings m valid.2 0
    (by simp [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.Pattern.variables]) (by decide +kernel) (m actual).1).mpr
  intro bounds member
  change bounds ∈ [(2,2),(2,2)] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact GeneralDictionaryVersionedUniversal231.actual_fits valid.1
  · cases List.mem_singleton.mp member
    exact GeneralDictionaryVersionedUniversal231.actual_fits valid.1

theorem packet_holds (valid : InstallationModels m) : GeneralNominalVersionedPlans231.Holds currentPlan m := by
  refine ⟨valid.1.1,⟨ordinary valid.2,GeneralDictionaryVersionedUniversal231.projection valid.1,?_,
    input_fits valid,GeneralDictionaryVersionedUniversal231.head_holds valid.1,?_,?_⟩,
    GeneralDictionaryVersionedUniversal231.outputs valid.1⟩
  · exact GeneralNominalCenters.point_root_holds snapshot.seed root root_point m
  · intro equation member _
    exact GeneralDictionaryVersionedUniversal231.outputs valid.1 equation member
  · intro clause member; cases member

theorem class_effects (valid : InstallationModels m) :
    GeneralNominalVersionedEffects231.ClassEffects after.core root currentPlan m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryUpper230Selected.request_exact member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    have out := GeneralDictionaryVersionedUniversal231.outputs valid.1
    unfold GeneralNominalVersionedPlans231.Outputs at out
    rw [GeneralDictionaryVersionedPacket231.emitted_schema] at out
    have outEq := out ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
    change Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value at outEq ⊢
    exact outEq
  · intro first one last two _
    cases GeneralDictionaryUpper230Selected.request_exact one
    cases GeneralDictionaryUpper230Selected.request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem certificate (valid : InstallationModels m) :
    GeneralNominalVersionedEvidence231.Certificate registry after.core m root declaration.id [] currentPlan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics GeneralDictionaryVersionedEvidence231.frame
    GeneralDictionaryVersionedEvidence231.children_empty.symm (packet_holds valid) ready (class_effects valid)

theorem evidence (valid : InstallationModels m) :
    GeneralNominalVersionedEvidence231.Evidence registry after.core m root (.node declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨currentPlan,certificate valid⟩

theorem inhabited : ∃ m, InstallationModels m :=
  ⟨extended,retains_journal,GeneralDictionaryVersionedMerge231.merge_model⟩

theorem nonvacuous_modelwise_completion :
    (∃ m, InstallationModels m) ∧ ∀ m, InstallationModels m →
      GeneralNominalVersionedEvidence231.Evidence registry after.core m root (.node declaration.id []) :=
  ⟨inhabited,fun _ => evidence⟩
end Yulang.GeneralDictionaryVersionedCompletion231
