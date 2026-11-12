import Yulang.GeneralNominalSupportSteps
import Yulang.GeneralNominalOutputGrowthMeasures
import Yulang.GeneralNominalSupportBoundary

/-! The first output-grown child is blocked even after the real certified
refresh. Its ordinary and named equations remain in the complete model set. -/
namespace Yulang.GeneralNominalSupportGrowth

open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalOutputGrowth GeneralNominalOutputGrowthModels GeneralNominalOutputGrowthPackets
open GeneralNominalOutputGrowthRefresh
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev start : Tracked roles := GeneralNominalSupport.initial (context 0) (root 0)
noncomputable def added : Tracked roles := GeneralNominalSupportSteps.install start (packet 0) []
noncomputable def observed : Tracked roles := {added with current := refreshed}

private theorem reads_root : readsMany (source 0)
    (GeneralNominalInspection.queries (source 0) (context 0).interpretation declaration) (bounds 0) = [slot 0] := by
  have query : GeneralNominalInspection.queries (source 0) (context 0).interpretation declaration =
      [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,source]
  rw [query]
  simp [readsMany.eq_def,reads.eq_def,bounds,slot,source,descriptor,GeneralNominalRecursiveInspection.typeArguments]

private theorem initial_head : Head (source 0) 0 (.nominal 0 1)
    (.nominal (base 0) (slot 0) (descriptor 0 (slot 0) (Nat.le_refl _))) :=
  Head.nominal (snapshot := source 0) (slot 0) (descriptor 0 (slot 0) (Nat.le_refl _)) rfl

theorem root_guard : PacketGuard start (packet 0) [] := by
  have single : Guard start (root 0) declaration (bounds 0) [] := by
    apply source_guard
    · intro index
      exact ⟨_,_,_,initial_head,initial_head⟩
    · intro slot member
      dsimp only [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] at member ⊢
      rw [reads_root] at member
      have same := List.mem_singleton.mp member; subst slot
      exact ⟨_,_,_,initial_head,initial_head⟩
  refine ⟨single,single.1,single.2.1,?_⟩
  intro candidate visible role intervals found
  have same := List.mem_singleton.mp visible; subst candidate
  have equal := Option.some.inj ((located 0).symm.trans found); subst intervals
  exact single.2.2

theorem first_install : Step registry (root 0) start added := by
  refine ⟨root 0,.root,.install (packet 0) [] (enabled 0) ?_ root_guard⟩
  intro committed
  have absent := committed.2 (child 0) (by rw [children_exact]; simp)
  cases absent

theorem first_refresh : Step registry (root 0) added observed := by
  refine ⟨child 0,?_,.administrative (child 0) _
    (.refresh (child 0) refreshedContext refresh_certificate 1 ?_ ?_ child_known)⟩
  · apply Generated.child .root
    change (root 0,child 0) ∈ [] ++ (packet 0).children.map _
    rw [children_exact]; simp [GeneralNominalDemandMerging.pointSite]
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨endpoint 0,rfl⟩)))
  · exact (child_pending 0).choose_spec

theorem formed : SourceFormed registry (root 0) observed :=
  .update (.update (.initial (context 0) (initial_source 0)) first_install) first_refresh

theorem full_models (model : GeneralNominalCommonBridge.Assignment) :
    Models observed.current model ↔ Models (installed 0) model := refresh_models model

/-- Finite discharge requires a leaf; committed non-leaf packets do not suffice. -/
theorem no_leaves_no_discharge (state : State roleDecls)
    (nonempty : ∀ packet ∈ state.packets, packet.children ≠ []) (focus : Occurrence roleDecls) :
    ¬ Discharged state focus := by
  intro done
  induction done with
  | packet packet member children ih =>
    cases listed : packet.children with
    | nil => exact nonempty packet member listed
    | cons child rest => exact ih child (by rw [listed]; simp)
  | alias _ _ _ _ _ _ ih => exact ih

theorem unresolved (focus : Occurrence roles) : ¬ Discharged observed.current focus := by
  apply no_leaves_no_discharge
  intro candidate member
  have same : candidate = packet 0 := List.mem_singleton.mp member
  subst candidate
  rw [children_exact]; simp

theorem dependency : Generated observed.current (root 0) (child 0) := by
  apply Generated.child .root
  change (root 0,child 0) ∈ [] ++ (packet 0).children.map _
  rw [children_exact]; simp [GeneralNominalDemandMerging.pointSite]

private theorem original_input (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (source 0) model) :
    GeneralNominalPacketSupport.Inputs (packet 0) model := by
  have query : GeneralNominalInspection.queries (source 0) (context 0).interpretation declaration =
      [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,source]
  have original := GeneralNominalUnaryCaptureFacts.private_models (context 0) registry (root 0)
    declaration (slot 0) (descriptor 0 (slot 0) (Nat.le_refl _)) rfl 0 rfl (endpoint 0,endpoint 0) rfl query model valid
  refine ⟨((GeneralNominalPacketSupport.private_exact (packet 0) model).mp original.1).2,original.2,?_⟩
  have empty : GeneralNominalPacketSupport.inputSchema (packet 0) = {} := by
    unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
      GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      List.mergeSort_singleton]
    simp [List.ofFn_succ,GeneralDeclarationDemands.emitAll,
      GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,
      GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated]
  rw [empty]
  exact GeneralNominalMaterialization.empty_models ..

theorem cut_model (support : List (Occurrence roles)) (allowed : Admissible observed (child 0) support) :
    Slice observed support (finiteModel 0) := by
  have excluded := cycle_excluded observed (child 0) (root 0) dependency (unresolved _) support allowed
  have original := (source_models 0 _).mpr (finite_prefix_models 0)
  refine ⟨original,?_⟩
  intro fact member included
  change fact ∈ GeneralNominalSupportChoices.installedFacts start (packet 0) ++ [] at member
  rw [GeneralNominalSupportChoices.empty_alternatives start (packet 0) rfl root_guard] at member
  simp only [List.append_nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact original_input _ original
  · exact False.elim (excluded (included (root 0) (by simp [Fact.dependencies,GeneralNominalDemandMerging.pointSite])))

private theorem int_not_nominal (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal 0 arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

private theorem nominal_holds {snapshot : GeneralNominalState.State} {identity name arity : Nat} {observation : GeneralCanonicalObservations.Observation}
    (head : Head snapshot identity (.nominal name arity) observation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : observation.Holds model) :
    ∃ arguments, Equivalent (model identity).1 (nominal name arguments) := by
  generalize tagEq : Test.nominal name arity = tag at head
  cases head with
  | scalar => cases tagEq
  | structural => cases tagEq
  | nominal slot descriptor recorded =>
    cases tagEq
    obtain ⟨arguments,_,equal⟩ := valid
    exact ⟨arguments,equal⟩

theorem child_head_unsupported (support : List (Occurrence roles))
    (allowed : Admissible observed (child 0) support) :
    ¬ HeadSupported observed support 1 (.nominal 0 1) := by
  rintro ⟨snapshot,observation,head,entailed⟩
  have valid := entailed (finiteModel 0) (cut_model support allowed)
  obtain ⟨arguments,equal⟩ := nominal_holds head _ valid
  exact int_not_nominal arguments equal.1

private theorem source_one {slot : Fin 3} (equal : identifiers slot = 1) : slot = 1 := by
  apply Fin.ext
  have fresh := output_fresh 0
  simp only [identifiers] at equal
  split at equal <;> omega

theorem child_not_ready (support : List (Occurrence roles))
    (allowed : Admissible observed (child 0) support) : ¬ ReadyAt observed support 1 := by
  rintro ⟨test,observation,head,supported⟩
  generalize identityEq : (1 : Nat) = identity at head supported
  cases head with
  | scalar slot base recorded =>
    have same := source_one identityEq.symm
    subst slot; cases recorded
  | structural slot kind children recorded => exact Fin.elim0 kind
  | nominal slot descriptor recorded =>
    have same := source_one identityEq.symm
    subst slot
    have equal : descriptor = lastDescriptor := (Option.some.inj recorded).symm
    subst descriptor
    exact child_head_unsupported support allowed supported

theorem child_guard_blocked (declaration : GeneralDeclarations.Declaration)
    (bounds : List (GeneralNominalInspection.Bounds observed.current.context.state)) (support : List (Occurrence roles)) :
    ¬ Guard observed (child 0) declaration bounds support := by
  rintro ⟨allowed,roots,_⟩
  exact child_not_ready support allowed (roots ⟨0,by decide⟩)

theorem child_final_pending : GeneralNominalSupportBoundary.Local registry observed (child 0) .pending := by
  apply GeneralNominalSupportBoundary.support_pending registry observed (child 0) child_ready
  · rintro ⟨support,allowed,roots,_⟩
    exact child_not_ready support allowed (roots ⟨0,by decide⟩)
  · exact child_not_rootK2
  · exact child_not_candidateK2

theorem no_modelwise_guarded_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Ty → Measure) :
    ¬ (∀ model, Models added.current model →
      less (rank (model ((child 0).demand.arguments ⟨0,by decide⟩).1).1)
        (rank (model ((root 0).demand.arguments ⟨0,by decide⟩).1).1)) :=
  no_modelwise_child_rank less wellFounded rank 0

end Yulang.GeneralNominalSupportGrowth
