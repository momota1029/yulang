import Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Local

/-! Port of the dot cycle-199 fixture at 45f6868be; original source identities
and declarations are retained in a separate namespace. -/

set_option backward.isDefEq.respectTransparency false

/-! Exact prior-interface counterexample: output-conflicting terminal head at an
inhabited reachable stable state. This does not claim a V6 selected frontier. -/
namespace Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Fixture
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Local
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepBoundary (boundary)

theorem output_request :
    (⟨.app 0 [.app 2 []],2,.actual⟩ : GeneralNominalMaterialization.Request) ∈
      GeneralNominalCenteredHeadMatSchemas.requests snapshot registry root declaration declaration_checked packet.bindings := by
  apply List.mem_append_left
  simp [GeneralNominalMaterialization.rootRequests]

theorem no_packet (assignment : GeneralNominalCommonBridge.Assignment) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment := by
  intro holds
  have equation := GeneralNominalCenteredHeadMatStepPackets.output_equation holds.2.2 output_request
    (show GeneralNominalCenteredHeadMatExpressions.translate GeneralDeclarationExamples.constructors context.interpretation
      (.app 0 [.app 2 []]) = some (.nominal 0 [.primitive (.scalar .int) []]) from rfl)
  have scalar := GeneralNominalCenteredTerminalForkSource.scalar assignment holds.1 2 (by decide +kernel)
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 _ (subtype_trans scalar.2 equation.1)

theorem no_install (candidate : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (focus : candidate.plan.packet.site.occurrence = root) : ¬ Installable registry start candidate := by
  intro enabled
  have framed := focus ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ candidate.frame
  have same := frame_plan framed
  obtain ⟨assignment,_,packet,_⟩ := enabled.common
  rw [same] at packet
  exact no_packet assignment packet

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

theorem request_here : (⟨0,2⟩ : GeneralSourceState.Output) ∈
    GeneralNominalCenteredHeadOutputs.requests start.core root :=
  GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr
    ⟨_,List.mem_singleton_self _,.refl _,List.mem_singleton_self _⟩

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root) :
    output = ⟨0,2⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root plan :=
  GeneralNominalCenteredHeadMatEffects.ready_of_wf coverage (List.mem_singleton_self _) rfl (by
    intro output member
    cases request_exact member
    exact ⟨none,rfl⟩)

theorem no_effects (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    ¬ GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan assignment := by
  intro effects
  have body := effects.1 ⟨0,2⟩ request_here (.explicit ⟨43,0,.app 0 [.app 2 []]⟩) rfl
  have equation := (GeneralNominalCenteredHeadMatEffects.body_equation
    (plan := plan) (body := .explicit ⟨43,0,.app 0 [.app 2 []]⟩)
    (show GeneralNominalCenteredHeadMatEffects.compileBody plan (.explicit ⟨43,0,.app 0 [.app 2 []]⟩) =
      some (.nominal 0 [.primitive (.scalar .int) []]) from rfl)).mp body
  have scalar := GeneralNominalCenteredTerminalForkSource.scalar assignment valid 2 (by decide +kernel)
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 _ (subtype_trans scalar.2 equation.1)

theorem output_conflict : (boundary roles).OutputConflict registry start root 37 := by
  constructor
  · exact ⟨model,inhabited,⟨children,unique⟩,plan,frame,ready,head_equations⟩
  · rintro ⟨assignment,valid,_,candidate,framed,_,_,effects⟩
    rw [frame_plan framed] at effects
    exact no_effects assignment valid.1 effects

/-- The corrected V6 classifier explicitly rejects the same counterexample. -/
theorem rejected : GeneralNominalCenteredHeadMatStepBoundary.Local registry start root .rejected :=
  B4TargetV6.output_conflict_rejected safe unique output_conflict

end Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Fixture
