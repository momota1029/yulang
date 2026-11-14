import Yulang.GeneralDictionaryCenteredNominalExample178
import Yulang.GeneralDictionaryNominalPairSupport178
import Yulang.GeneralNominalCenteredModelExtension

/-! A centered model also assigns the actual binder center; the raw branch
model alone does not fix it. This finite extension preserves all old sources. -/
namespace Yulang.GeneralDictionaryNominalPairJoint178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

abbrev binder : Nat := fresh GeneralDictionaryNominalPairExample178.state.seed GeneralDictionaryCenteredNominalExample178.root.identity GeneralDictionaryNominalPairExample178.declaration.id 8 0 0

theorem binder_old (i : Nat) (bounded : i ≤ 3) : binder ≠ i := by
  have above := GeneralNominalIdentities.source_above_seed GeneralDictionaryNominalPairExample178.state.seed
    (GeneralNominalAllocation.origin GeneralDictionaryCenteredNominalExample178.root.identity GeneralDictionaryNominalPairExample178.declaration.id 8 0 0)
  change 3 < binder at above
  omega

theorem binder_lo : binder ≠ GeneralDictionaryNominalPairExample178.lo := by
  intro same
  have eq := (GeneralNominalAllocation.source_identity GeneralDictionaryNominalPairExample178.state GeneralDictionaryNominalPairExample178.registry GeneralDictionaryCenteredNominalExample178.root.identity _ _).mp same
  cases eq

theorem binder_hi : binder ≠ GeneralDictionaryNominalPairExample178.hi := by
  intro same
  have eq := (GeneralNominalAllocation.source_identity GeneralDictionaryNominalPairExample178.state GeneralDictionaryNominalPairExample178.registry GeneralDictionaryCenteredNominalExample178.root.identity _ _).mp same
  cases eq

 theorem actual_binder : GeneralDictionaryCenteredNominalExample178.plan.binder 0 = binder := by
  decide +kernel

 def assignment : GeneralNominalCommonBridge.Assignment := fun i =>
  if i = binder then (.base .int,Common.rowEmpty) else GeneralDictionaryNominalPairExample178.assignment true i

 theorem old_value (i : Nat) (bounded : i ≤ 3) : assignment i = GeneralDictionaryNominalPairExample178.assignment true i := by
  simp [assignment,Ne.symm (binder_old i bounded)]
 theorem lower_value : assignment GeneralDictionaryNominalPairExample178.lo = GeneralDictionaryNominalPairExample178.assignment true GeneralDictionaryNominalPairExample178.lo := by simp [assignment,Ne.symm binder_lo]
 theorem upper_value : assignment GeneralDictionaryNominalPairExample178.hi = GeneralDictionaryNominalPairExample178.assignment true GeneralDictionaryNominalPairExample178.hi := by simp [assignment,Ne.symm binder_hi]
 theorem binder_value : (assignment binder).1 = .base .int := by simp [assignment]; rfl

 theorem source_models : GeneralNominalState.Models GeneralDictionaryNominalPairExample178.state assignment := by
  apply GeneralNominalCenteredModelExtension.source_models_same GeneralDictionaryNominalPairExample178.state _ (GeneralDictionaryNominalPairExample178.source_models true)
  intro name member
  have bounded : name ≤ 3 := by
    change name ∈ GeneralNominalState.sources GeneralDictionaryNominalPairExample178.state at member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    omega
  exact (old_value name bounded).symm

 theorem merges : PresenceNormalForm.All CommonNominalFullCarrier.model assignment
    (GeneralNominalAllocation.merges GeneralDictionaryNominalPairExample178.state GeneralDictionaryNominalPairExample178.registry GeneralDictionaryCenteredNominalExample178.root.identity GeneralDictionaryNominalPairExample178.declaration GeneralDictionaryNominalPairExample178.captures) := by
  rw [GeneralDictionaryNominalPairExample178.merges_exact,PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
    GeneralNominalCaptureMerges.equations_exact]
  have prior := GeneralDictionaryNominalPairExample178.merge_good
  rw [GeneralDictionaryNominalPairExample178.merges_exact,PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
    GeneralNominalCaptureMerges.equations_exact] at prior
  change Equivalent (assignment GeneralDictionaryNominalPairExample178.lo).1 (.union (assignment 2).1 (assignment 2).1) ∧
    Equivalent (assignment GeneralDictionaryNominalPairExample178.hi).1 (.inter (assignment 3).1 (assignment 3).1)
  rw [lower_value,upper_value,old_value 2 (by decide +kernel),old_value 3 (by decide +kernel)]
  exact prior

 theorem branch : GeneralDictionaryCenteredNominalExample178.packet.Holds assignment := by
  have ordered : Subtype (assignment 0).1 (assignment 1).1 := by
    rw [old_value 0 (by decide +kernel),old_value 1 (by decide +kernel)]
    exact GeneralDictionaryNominalPairExample178.endpoint_order true
  apply (GeneralDictionaryNominalPair178.branch_models_iff_merges GeneralDictionaryNominalPairExample178.context
    GeneralDictionaryNominalPairExample178.registry GeneralDictionaryCenteredNominalExample178.root
    GeneralDictionaryNominalPairExample178.declaration GeneralDictionaryCenteredNominalExample178.packet.checked
    GeneralDictionaryNominalPairExample178.shape rfl rfl assignment source_models ordered).mpr
  change PresenceNormalForm.All model assignment (GeneralNominalAllocation.merges GeneralDictionaryNominalPairExample178.state
    GeneralDictionaryNominalPairExample178.registry GeneralDictionaryCenteredNominalExample178.root.identity
    GeneralDictionaryNominalPairExample178.declaration (bindings GeneralDictionaryNominalPairExample178.state
    (report GeneralDictionaryNominalPairExample178.context GeneralDictionaryNominalPairExample178.declaration [(0,1)])))
  rw [GeneralDictionaryNominalPairExample178.report_captures]
  exact merges

 theorem head_schema : GeneralDictionaryCenteredNominalExample178.plan.headSchema =
    (⟨[⟨0,.nominal (.source 0) 0 0,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ : GeneralNominalMaterialization.Schema) := by
  simp [Plan.headSchema,GeneralDictionaryCenteredNominalExample178.plan,
    GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,List.ofFn_succ,
    GeneralNominalMaterialization.Schema.append]

 theorem inputs_empty : GeneralNominalPacketSupport.inputSchema GeneralDictionaryCenteredNominalExample178.packet = {} :=
  GeneralNominalSharedPositive.leaf_input_schema _ rfl
 theorem named_empty : GeneralNominalPacketSupport.namedSchema GeneralDictionaryCenteredNominalExample178.packet = {} :=
  GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ rfl rfl _

 theorem observed_int : Observes assignment (.nominal (.source 0) 0 0) (.base .int) := by
  apply Observes.nominal (arguments := [.inl (.base .int)]) (.source 0) _ rfl
  change Equivalent (assignment 0).1 (nominal 0 [.inl (.base .int)])
  rw [old_value 0 (by decide +kernel)]
  exact ⟨subtype_refl _,subtype_refl _⟩

 theorem observed_unique (actual : Ty) (seen : Observes assignment (.nominal (.source 0) 0 0) actual) :
    Equivalent actual (.base .int) :=
  GeneralNominalRecursiveInspection.nominal_observation_unique assignment
    (.argument (.source 0) 0 0) actual (.base .int) seen observed_int

 theorem centered_head : GeneralDictionaryCenteredNominalExample178.plan.SchemaHolds
    GeneralDictionaryCenteredNominalExample178.plan.headSchema assignment := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 0⟩,?_⟩
    intro actual seen
    cases seen
    change ∃ arguments, arguments.length = 1 ∧ Equivalent (assignment 0).1 (nominal 0 arguments)
    rw [old_value 0 (by decide +kernel)]
    exact ⟨[.inl (.base .int)],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true]
    refine ⟨⟨_,observed_int⟩,⟨_,.source _⟩,?_⟩
    intro a b one two
    cases two
    rw [actual_binder,binder_value]
    exact observed_unique a one

 theorem plan_holds : GeneralDictionaryCenteredNominalExample178.plan.Holds assignment := by
  refine ⟨branch,?_,?_,centered_head,?_,?_,?_⟩
  · intro index
    change Subtype (assignment 0).1 (assignment 0).1 ∧ Subtype (assignment 0).1 (assignment 1).1
    rw [old_value 0 (by decide +kernel),old_value 1 (by decide +kernel)]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name needed
    have zero : name = 0 := by
      rcases needed with input | ⟨clause,member,_⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables] using input
      · cases member
    subst name
    rw [actual_binder,binder_value]
    have capture : (GeneralNominalPacketSupport.capture GeneralDictionaryCenteredNominalExample178.plan.packet).inputs 0 =
        (GeneralDictionaryNominalPairExample178.lo,GeneralDictionaryNominalPairExample178.hi) := by decide +kernel
    rw [capture]
    unfold GeneralNominalCaptureMerges.Fits
    rw [lower_value,upper_value,GeneralDictionaryNominalPairExample178.fresh_lower_good,
      GeneralDictionaryNominalPairExample178.fresh_upper_good]
    exact ⟨(CommonNominalFullModelMap.subtype_exact .bottom (.base .int)).mpr (CommonBoundCoalescing.bottom_le _),
      GeneralNominalNonpointInspectionExamples.int_top⟩
  · rw [inputs_empty]; constructor <;> intro _ h <;> cases h
  · rw [named_empty]; constructor <;> intro _ h <;> cases h
  · intro clause member; cases member

 theorem joint_model : ∃ model, Models GeneralDictionaryCenteredNominalExample178.start model ∧
    GeneralDictionaryCenteredNominalExample178.plan.Holds model := by
  refine ⟨assignment,?_,plan_holds⟩
  apply (initialAt_models _ _ _).mpr
  exact ⟨source_models,plan_holds.2.1⟩

open GeneralDictionaryNominalPairExample178 (registry declaration context)
open GeneralDictionaryCenteredNominalExample178 (start root packet plan candidate prepared located)

 theorem value_guard : GeneralNominalValueSupport.PacketGuard start.erased packet [] :=
  GeneralDictionaryNominalPairSupport178.value_guard root (fun _ => rfl) packet.checked packet.site rfl located

 theorem raw_joint : GeneralNominalJointCandidates.Joint registry start.erased.current root declaration.id :=
  GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) packet.checked rfl
    [(0,1)] located prepared assignment branch

 theorem raw_installable
    (selected : GeneralNominalCenteredBoundary.Local registry start root (.selected declaration.id [])) :
    GeneralNominalFeedbackSteps.Installable registry start.erased.current packet := by
  have old : GeneralNominalFeedbackK2.Local registry start.erased.current root (.selected declaration.id []) := by
    cases selected with
    | selected safe unique =>
      exact .selected ⟨safe.1,fun h => safe.2.1 (.inl h),fun h => safe.2.2.1 (.inl h),
        fun h => safe.2.2.2 (.inl h)⟩ unique
  have kids : packet.children = [] := candidate.children_eq
  have closed : GeneralNominalFeedbackSteps.MergesClosed start.erased.current packet.site := by
    intro other member _
    have same : other = packet.site := List.mem_singleton.mp member
    subst other
    exact .refl _
  refine ⟨?_,?_,closed⟩
  · refine ⟨rfl,rfl,by simp [start,initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],
      by simp,rfl,located,prepared,?_,?_,?_,?_,raw_joint⟩
    · rw [kids]
      exact GeneralNominalFeedbackK2.selected_legacy old
    · intro prior member; cases member
    · intro other member _
      have same : other = packet.site := List.mem_singleton.mp member
      subst other; exact .refl _
    · exact ⟨assignment,GeneralNominalSaturationState.initial_models _ _ _ |>.mpr source_models,branch⟩
  · rw [kids]
    exact old

 theorem installable
    (selected : GeneralNominalCenteredBoundary.Local registry start root (.selected declaration.id [])) :
    GeneralNominalCenteredBoundary.Installable registry start plan :=
  ⟨raw_installable selected,[],(GeneralDictionaryCenteredGuard177.candidate_guard_iff candidate selected []).mpr
    ⟨value_guard,joint_model⟩⟩

/-- The bad fixed-model fixture cannot simultaneously be stable and selected:
all installation guards are produced, so stability would force the branch. -/
 theorem stable_not_selected : Stable registry start root →
    ¬ GeneralNominalCenteredBoundary.Local registry start root (.selected declaration.id []) := by
  intro stable selected
  have committed := GeneralDictionaryCenteredReady176.stable_committed stable plan rfl (installable selected)
  exact GeneralDictionaryCenteredNominalExample178.branch_bad
    (committed.1 (GeneralDictionaryNominalPairExample178.assignment false)
      (GeneralDictionaryCenteredNominalExample178.inhabited false).1)
end Yulang.GeneralDictionaryNominalPairJoint178
