import Yulang.GeneralNominalCenteredHeadMatCompletionCollisionPackets

set_option backward.isDefEq.respectTransparency false

/-! An actual WF ground initial state is selected and stable, yet its two
where requests cannot be installed because their allocated output targets
collide. The pre-state and the chosen class effects have a common model. -/
namespace Yulang.GeneralNominalCenteredHeadMatCompletionCollision
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatCompletionCollisionSource
open GeneralNominalCenteredHeadMatCompletionCollisionLocal
open GeneralNominalCenteredHeadMatCompletionCollisionPackets
open GeneralNominalCenteredHeadMatStepJournal (Models Effect)
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredHeadMatStepKernel

theorem no_install (candidate : Effect roles) (focus : candidate.plan.packet.site.occurrence = root) :
    ¬ Installable registry start candidate := by
  intro enabled
  have framed := focus ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ candidate.frame
  have same := frame_plan framed
  obtain ⟨assignment,_,packet,_⟩ := enabled.common
  rw [same] at packet
  exact no_packet_model assignment packet

theorem generated_only_root (focus : Occurrence roles)
    (generated : GeneralNominalSaturationState.Generated start.core.erased.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child prior member ih => cases member
  | alias prior one two same ih =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)

theorem stable : Stable registry start root := by
  intro focus generated after action
  have same := generated_only_root focus generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
        exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
        apply novel
        intro assignment sourceModels
        exact equal assignment ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models
          (fun _ => rfl)).mpr sourceModels)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
  | install candidate enabled novel => exact no_install candidate same enabled
  | merge first last one two inputs novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem halted : ∀ after, ¬ Step registry root start after := by
  rintro after ⟨focus,generated,action⟩
  exact stable focus generated after action

theorem children_length : children.length = 2 := by
  change packet.children.length = 2
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_declaration]
  simp [GeneralDeclarationDemands.emitAll]

theorem child_ne_root (child : Occurrence roles) (member : child ∈ children) : child ≠ root := by
  obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child member
  have role : clause.role ≠ 0 := by
    rcases List.mem_cons.mp present with rfl | present
    · decide +kernel
    · cases List.mem_singleton.mp present; decide +kernel
  intro same
  exact role (congrArg (fun occurrence : Occurrence roles => occurrence.demand.role) same)

theorem child_not_generated (child : Occurrence roles) (member : child ∈ children) :
    ¬ GeneralNominalSaturationState.Generated start.core.erased.current root child :=
  fun generated => child_ne_root child member (generated_only_root child generated)

theorem choice_compatible : GeneralNominalCycleSteps.ChoiceCompatible start.core.erased.current effect.plan.packet := by
  intro prior member; cases member

theorem not_selectedCompletion : ¬ GeneralNominalCenteredHeadMatStepCompletion.SelectedCompletion roles := by
  intro complete
  obtain ⟨candidate,registryEq,snapshot,focus,key,kids,extension⟩ :=
    complete registry ⟨rfl,checked⟩ start root root 37 children reachable selected
  have framed := focus ▸ snapshot ▸ registryEq ▸ candidate.frame
  have same := frame_plan framed
  obtain ⟨assignment,_,packet,_⟩ := extension.2
  rw [same] at packet
  exact no_packet_model assignment packet

theorem not_generatedSelectedChildren :
    ¬ GeneralNominalCenteredHeadMatStepCompletion.GeneratedSelectedChildren roles := by
  intro production
  have nonempty : children ≠ [] := by
    intro empty
    have count := children_length
    rw [empty] at count
    contradiction
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact child_not_generated child member
    (production registry ⟨rfl,checked⟩ start root root 37 children reachable stable .root selected child member)

theorem not_prior_generatedChildren :
    ¬ B4SkeletonV5.GeneratedChildren (B4TargetV6.prior (boundary roles)) := by
  intro production
  have nonempty : children ≠ [] := by
    intro empty
    have count := children_length
    rw [empty] at count
    contradiction
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact child_not_generated child member
    (production registry ⟨rfl,checked⟩ start root root 37 children reachable (Or.inl rfl) stable safe unique child member)

theorem stable_selected_counterexample :
    (boundary roles).Checked registry ∧ (boundary roles).Initial registry root start ∧
    B4TargetV6.Reachable (boundary roles) registry root start ∧ Stable registry start root ∧
    Local registry start root (.selected 37 children) ∧ children.length = 2 ∧
    (∃ assignment, Models start assignment ∧ effect.Holds assignment) ∧
    (∃ assignment, Models start assignment ∧
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead registry start root 37 assignment) ∧
    ¬ GeneralNominalCenteredHeadMatStepLocal.OutputConflict registry start root 37 ∧
    GeneralNominalCycleSteps.ChoiceCompatible start.core.erased.current effect.plan.packet ∧
    (∀ candidate : Effect roles, candidate.plan.packet.site.occurrence = root → ¬ Installable registry start candidate) ∧
    (∀ child ∈ children, ¬ GeneralNominalSaturationState.Generated start.core.erased.current root child) :=
  ⟨⟨rfl,checked⟩,initial_source,reachable,stable,selected,children_length,⟨model,effect_model⟩,
    positive_baseline,no_output_conflict,choice_compatible,no_install,child_not_generated⟩

end Yulang.GeneralNominalCenteredHeadMatCompletionCollision
