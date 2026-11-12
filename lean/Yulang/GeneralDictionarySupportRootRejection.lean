import Yulang.GeneralDictionarySupportPointRefresh

/-! The root of the concrete revised/point-refreshed path is rejected, not
selected. The journal forces its nominal argument to be equivalent to itself.
This uses the actual feedback graph and an inhabited model set. -/
namespace Yulang.GeneralDictionarySupportRootRejection
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralDictionaryCurrentRevisionObstruction
open GeneralDictionarySupportRevisionStability
open GeneralDictionarySupportPointRefresh
open GeneralNominalReobservationSteps
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier GeneralDeclarations

/-- Slot0 and source2 denote the same self-recursive nominal value. -/
theorem root_equal (m : GeneralNominalCommonBridge.Assignment) (valid : Models after.current m) :
    Equivalent (m 0).1 (m 2).1 := by
  have zero := valid.1.2.1 (0 : Fin 4) point (by rfl)
  have two := valid.1.2.1 (2 : Fin 4) point (by rfl)
  have zero := (GeneralNominalState.denotes_singleton_exact after.current.context.state.base
    m (0 : Fin 4) (2 : Fin 4) point rfl).mp zero
  have two := (GeneralNominalState.denotes_singleton_exact after.current.context.state.base
    m (2 : Fin 4) (2 : Fin 4) point rfl).mp two
  exact ⟨subtype_trans zero.1 two.2,subtype_trans two.1 zero.2⟩

/-- Semantic equality closes a genuine nominal argument edge into a cycle. -/
theorem root_self_argument : GeneralNominalFeedbackK2.Argument after.current 0 0 := by
  refine ⟨0,0,?_⟩
  intro m valid
  have zero := valid.1.2.1 (0 : Fin 4) point (by rfl)
  have zero := (GeneralNominalState.denotes_singleton_exact after.current.context.state.base
    m (0 : Fin 4) (2 : Fin 4) point rfl).mp zero
  have same := root_equal m valid
  exact ⟨(m 2).1,.argument (.source 0) zero rfl,⟨same.2,same.1⟩⟩

theorem root_linked : GeneralNominalState.Linked after.current.context.state root.demand := by
  constructor
  · intro index
    have supported : 0 ∈ GeneralNominalState.sources after.current.context.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨(0 : Fin 4),rfl⟩)))
    exact ⟨supported,supported⟩
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨(2 : Fin 4),rfl⟩)))

theorem root_ready : ¬ GeneralNominalState.RootPending after.current.context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨point,rfl⟩⟩

theorem root_K2 : GeneralNominalFeedbackK2.RootK2 after.current root :=
  GeneralNominalFeedbackK2.root_self_argument after.current root root_linked root_ready
    (0 : Fin 1) root_self_argument model ((models_iff model).mpr point_models)

theorem root_rejected : GeneralNominalSupportBoundary.Local registry after root .rejected :=
  .rejected ⟨root_ready,Or.inl root_K2⟩

theorem root_not_selected (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalSupportBoundary.Local registry after root (.selected key children) := by
  intro selected
  have impossible := GeneralNominalLocalBoundary.local_functional root_rejected selected
  cases impossible


/-- Already in the original cycle147 revised snapshot, the journal provides
source2's self-equation without waiting for its explicit Known descriptor. -/
theorem original_root_self_argument : GeneralNominalFeedbackK2.Argument
    GeneralDictionarySupportRevisionObstruction.finish.current 0 0 := by
  refine ⟨0,0,?_⟩
  intro m valid
  have zero := valid.1.2.1 (0 : Fin 4) point (by rfl)
  have zero := (GeneralNominalState.denotes_singleton_exact revised.context.state.base
    m (0 : Fin 4) (2 : Fin 4) point rfl).mp zero
  have held : packet.Holds m := valid.2.1 packet (by
    simp [revised,Revision.result,
      regenerate,installed,GeneralNominalFeedbackSites.install])
  have two := GeneralNominalFeedbackRefresh.self_equation m held
  have same : Equivalent (m 2).1 (m 0).1 :=
    ⟨subtype_trans two.1 zero.2,subtype_trans zero.1 two.2⟩
  exact ⟨(m 2).1,.argument (.source 0) zero rfl,same⟩

theorem original_root_ready : ¬ GeneralNominalState.RootPending
    GeneralDictionarySupportRevisionObstruction.finish.current.context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨point,rfl⟩⟩

theorem original_root_K2 : GeneralNominalFeedbackK2.RootK2
    GeneralDictionarySupportRevisionObstruction.finish.current root :=
  GeneralNominalFeedbackK2.root_self_argument _ root root_linked original_root_ready
    (0 : Fin 1) original_root_self_argument model
    GeneralDictionarySupportRevisionObstruction.modeled_nonempty.1

/-- The original emission-gap example fails the actual selected premise too. -/
theorem original_root_rejected : GeneralNominalSupportBoundary.Local registry
    GeneralDictionarySupportRevisionObstruction.finish root .rejected :=
  .rejected ⟨original_root_ready,Or.inl original_root_K2⟩

theorem original_root_not_selected (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalSupportBoundary.Local registry
      GeneralDictionarySupportRevisionObstruction.finish root (.selected key children) := by
  intro selected
  have impossible := GeneralNominalLocalBoundary.local_functional original_root_rejected selected
  cases impossible


theorem point_root_K2 : GeneralNominalFeedbackK2.RootK2 pointFinish.current root := by
  have argument : GeneralNominalFeedbackK2.Argument pointFinish.current 0 0 := by
    obtain ⟨name,index,observes⟩ := original_root_self_argument
    exact ⟨name,index,fun m valid => observes m ((point_models_iff m).mp valid)⟩
  have ready : ¬ GeneralNominalState.RootPending pointFinish.current.context.state root.demand := by
    rintro ⟨index,unknown⟩
    exact unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨point,rfl⟩⟩
  exact GeneralNominalFeedbackK2.root_self_argument _ root root_linked ready
    (0 : Fin 1) argument model point_models

theorem point_root_rejected : GeneralNominalSupportBoundary.Local registry pointFinish root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.root_ready point_root_K2,Or.inl point_root_K2⟩

theorem point_root_not_selected (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralNominalSupportBoundary.Local registry pointFinish root (.selected key children) := by
  intro selected
  have impossible := GeneralNominalLocalBoundary.local_functional point_root_rejected selected
  cases impossible

end Yulang.GeneralDictionarySupportRootRejection
