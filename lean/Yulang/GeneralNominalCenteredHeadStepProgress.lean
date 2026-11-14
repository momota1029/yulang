import Yulang.GeneralNominalCenteredHeadStepBoundary

set_option backward.isDefEq.respectTransparency false

/-! The existing missing-fact measure applies to the repaired relation.
The source-to-finite-cover producer is an explicit remaining hypothesis. -/
namespace Yulang.GeneralNominalCenteredHeadStepProgress
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalSaturationState (Generated)
open GeneralNominalSharedBudget (Signature Represents)
open GeneralNominalCenteredAccessibility (Fact facts signature_mem known_mem equal_mem point_mem alias_mem)
variable {roles : Roles.RoleDecls} {state before after : State roles}

abbrev Recorded (state : State roles) (root : Occurrence roles) := GeneralNominalCenteredTrace.Recorded state.core root

theorem recorded_at (recorded : Recorded before root) (action : At registry before focus after) : Recorded after root := by
  cases action with
  | administrative focus after action =>
      have sites := (GeneralNominalReobservationSteps.at_extends (GeneralNominalSupportSteps.administrative_old action)).journal.sites
      have edges : after.edges = before.core.erased.current.edges := by cases action <;> rfl
      obtain ⟨site,member,same⟩ := recorded.1
      refine ⟨⟨site,sites site member,same⟩,?_⟩
      intro parent child member
      change (parent,child) ∈ after.edges at member
      rw [edges] at member
      obtain ⟨site,present,same⟩ := recorded.2 parent child member
      exact ⟨site,sites site present,same⟩
  | refresh | merge => exact recorded
  | install plan support enabled novel =>
      obtain ⟨site,member,same⟩ := recorded.1
      refine ⟨⟨site,List.mem_append_left _ member,same⟩,?_⟩
      intro parent child member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨site,present,same⟩ := recorded.2 parent child old
        exact ⟨site,List.mem_append_left _ present,same⟩
      · obtain ⟨actual,present,equal⟩ := List.mem_map.mp added
        cases equal
        exact ⟨GeneralNominalSharedEmission.childSite plan.packet child,
          List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩),rfl⟩

theorem recorded_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Recorded state root := by
  induction path with
  | refl => exact ⟨⟨_,List.mem_singleton_self _,rfl⟩,by intro _ _ impossible; cases impossible⟩
  | tail path step ih => exact recorded_at ih step.choose_spec.2

theorem generated_registered (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.core.erased.current root focus) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus := by
  have recorded := recorded_trace path
  cases generated with
  | root => exact recorded.1
  | child _ member => exact recorded.2 _ _ member
  | alias _ _ member _ => exact ⟨_,member,rfl⟩

theorem point_at (action : At registry before focus after)
    (point : GeneralNominalReobservationOrder.Point before.core.erased.current source) :
    GeneralNominalReobservationOrder.Point after.core.erased.current source := by
  cases action with
  | administrative focus after action =>
      exact GeneralNominalReobservationOrder.point_at (GeneralNominalSupportSteps.administrative_old action) point
  | refresh focus context certificate source member unknown known =>
      exact GeneralNominalReobservationOrder.point_refines certificate.refines point
  | merge => exact point
  | install plan support enabled novel =>
      have refinement := GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
        plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds
      conv at refinement => lhs; rw [enabled.frame.context_eq]
      exact GeneralNominalReobservationOrder.point_refines refinement point

def Holds (state : State roles) (fact : Fact roles) : Prop := GeneralNominalCenteredAccessibility.Holds state.core fact

theorem monotone (step : Step registry root before after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  have growth := at_extends step.choose_spec.2
  cases fact with
  | signature signature =>
      intro known
      exact ⟨fun model valid => known.1 model (growth.journal.models model valid),
        fun child member => growth.journal.edges _ (known.2 child member)⟩
  | known => exact growth.journal.known _
  | equal => exact fun prior model valid => prior model (growth.ordinary model valid)
  | alias first last => exact GeneralNominalSaturationProgress.monotone growth.journal (.alias first last)
  | point => exact point_at step.choose_spec.2

structure FiniteCover (registry : Registry) (root : Occurrence roles) (start : State roles) where
  signatures : List (Signature roles)
  sources : List Nat
  occurrences : List (Occurrence roles)
  installs : ∀ state, B4Target.Steps (Step registry root) start state → ∀ plan support,
    Generated state.core.erased.current root plan.packet.site.occurrence →
    Installable registry state plan support →
    ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet →
    ∃ signature ∈ signatures, Represents signature plan.packet
  source_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    GeneralNominalState.sources state.core.erased.current.context.state ⊆ sources
  slot_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ slot, state.core.erased.current.context.state.base.source slot ∈ sources
  center_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ site ∈ state.core.sites, site.occurrence ∈ occurrences

theorem novel_signature (enabled : Installable registry state plan support)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet)
    (represents : Represents signature plan.packet) : ¬ Holds state (.signature signature) := by
  intro held
  apply novel
  refine ⟨?_,?_⟩
  · intro model valid
    apply (GeneralNominalPacketSupport.packet_exact plan.packet model).mpr
    refine ⟨?_,(represents.2.2 model).mp (held.1 model valid)⟩
    simpa only [enabled.frame.context_eq] using valid.1
  · intro child member
    simpa only [represents.1] using held.2 child (represents.2.1.symm ▸ member)

theorem fresh_fact (cover : FiniteCover registry root (initial context root))
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (step : Step registry root before after) :
    ∃ fact ∈ facts cover.signatures cover.sources cover.occurrences, ¬ Holds before fact ∧ Holds after fact := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install plan support enabled novel =>
      obtain ⟨signature,member,represented⟩ := cover.installs before path plan support generated enabled novel
      exact ⟨.signature signature,signature_mem member,novel_signature enabled novel represented,
        GeneralNominalSharedBudget.installed_signature represented support⟩
  | refresh focus context certificate identity member unknown known =>
      exact ⟨.known identity,known_mem (cover.source_mem before path member),unknown,known⟩
  | merge first last support one two same novel guard =>
      exact ⟨.alias first.occurrence.identity last.occurrence.identity,
        alias_mem (cover.center_mem before path first one) (cover.center_mem before path last two),novel,
        GeneralNominalCycleSteps.merged_inputs before.core.erased.current first.observed last.observed⟩
  | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
          obtain ⟨site,member,same⟩ := generated_registered path generated
          exact False.elim (absent site member same)
      | refresh context certificate identity member unknown known =>
          exact ⟨.known identity,known_mem (cover.source_mem before path member),unknown,known⟩
      | equate first last one two equal novel =>
          exact ⟨.equal first last,equal_mem (cover.source_mem before path one) (cover.source_mem before path two),novel,
            GeneralNominalFeedbackSteps.equate_feedback before.core.erased.current first last⟩
      | reobserve revision certificate improved =>
          obtain ⟨slot,old,now⟩ := improved.2
          refine ⟨.point (before.core.erased.current.context.state.base.source slot),
            point_mem (cover.slot_mem before path slot),?_,slot,rfl,now⟩
          rintro ⟨other,same,point⟩
          have equal := before.core.erased.current.context.state.base.source_injective same
          exact old (equal ▸ point)

theorem accessible_of_cover (cover : FiniteCover registry root (initial context root)) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalFiniteProgress.accessible (Step registry root) (initial context root) Holds
    (facts cover.signatures cover.sources cover.occurrences)
    (fun _ _ step => monotone step) (fun _ _ path step => fresh_fact cover path step)

def GroundCover (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles) labels,
    GeneralNominalSourceFormation.InitialSource registry context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels →
    Nonempty (FiniteCover registry root (initial context root))

theorem progress (covers : GroundCover roles) (registry : Registry)
    (checked : (GeneralNominalCenteredHeadStepBoundary.boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadStepBoundary.boundary roles) registry root state) :
    Acc (fun next current => Step registry root current next) state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  obtain ⟨cover⟩ := covers registry checked.2 context root labels source point ground
  have accessible := accessible_of_cover cover
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

end Yulang.GeneralNominalCenteredHeadStepProgress
