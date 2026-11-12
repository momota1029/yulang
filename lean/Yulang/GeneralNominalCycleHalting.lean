import Yulang.GeneralNominalCycleSteps

/-! The old nominal self-cycle cannot start an expansion under the new Step.
The proof checks all update constructors, not just the local rejection. -/
namespace Yulang.GeneralNominalCycleHalting

open GeneralNominalSaturationState GeneralNominalCycleSteps
open GeneralSourceDictionaries

theorem initial_generated (context : GeneralNominalCandidates.Context) (root focus : Occurrence roles)
    (generated : Generated (initial context root) root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

theorem cycle_initial_halted (registry : GeneralDeclarations.Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (cycle : GeneralNominalCycleK2.RootK2 context.state root.demand)
    (known : ∀ source ∈ GeneralNominalState.sources context.state, GeneralNominalState.Known context.state source) :
    ∀ after, ¬ Step registry root (initial context root) after := by
  rintro after ⟨focus,generated,update⟩
  have same := initial_generated context root focus generated
  cases update with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install packet emitted enabled novel =>
    have rootCycle : GeneralNominalCycleK2.RootK2 (initial context root).context.state packet.site.occurrence.demand := by
      rw [same]; exact cycle
    exact rootK2_never_installed registry _ packet rootCycle enabled
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one; have b := List.mem_singleton.mp two
    subst first; subst last; exact novel (.refl _)
  | refresh _ _ _ source member unknown _ => exact unknown (known source member)

theorem cycle_initial_accessible (registry : GeneralDeclarations.Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (cycle : GeneralNominalCycleK2.RootK2 context.state root.demand)
    (known : ∀ source ∈ GeneralNominalState.sources context.state, GeneralNominalState.Known context.state source) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  Acc.intro _ (fun after update => False.elim (cycle_initial_halted registry context root cycle known after update))

theorem obstruction_step_accessible (invocation : Nat) :
    Acc (fun next current => Step GeneralNominalProgressObstruction.registry
      (GeneralNominalProgressObstruction.root invocation) current next)
      (initial GeneralNominalProgressObstruction.context (GeneralNominalProgressObstruction.root invocation)) := by
  apply cycle_initial_accessible _ _ _ (GeneralNominalCycleRegressions.nominal_cycle_K2 invocation)
  intro source member
  have zero : source = 0 := by
    simpa [GeneralNominalState.sources,List.ofFn_succ] using member
  subst source
  exact ⟨0,rfl,Or.inr ⟨GeneralNominalProgressObstruction.descriptor,rfl⟩⟩

end Yulang.GeneralNominalCycleHalting
