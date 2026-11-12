import Yulang.GeneralDictionarySupportRevisionStability
import Yulang.GeneralNominalFeedbackRefresh

/-! Point-closed does not mean globally stable. The concrete continued state
still admits an exact journal-justified refresh at previously unknown source2.
No existing rule or meaning is changed. -/
namespace Yulang.GeneralDictionarySupportPointRefresh
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralDictionaryCurrentRevisionObstruction
open GeneralDictionarySupportRevisionStability
open GeneralNominalFeedbackRefresh (descriptor self_equation)
open GeneralNominalReobservationSteps
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier GeneralDeclarations
noncomputable def refreshedState : GeneralNominalState.State :=
  { twiceRevised.context.state with
    nominals := fun slot => if slot.val = 2 then some descriptor else twiceRevised.context.state.nominals slot
    catalogue := by
      intro slot d recorded
      split at recorded
      · have same := Option.some.inj recorded; subst d; rfl
      · exact twiceRevised.context.state.catalogue slot d recorded
    bodies_opaque := by intro _ _ _; rfl }

noncomputable def refreshedContext : GeneralNominalCandidates.Context := ⟨refreshedState,context.interpretation⟩
noncomputable def refreshed := regenerate twiceRevised refreshedContext

noncomputable def refines : GeneralNominalRefinements.Refines twiceRevised.context.state refreshedState := by
  have retained : ∀ slot d, twiceRevised.context.state.nominals slot = some d → refreshedState.nominals slot = some d := by
    intro slot d recorded
    have different : slot.val ≠ 2 := by
      intro two
      have same : slot = (2 : Fin 4) := Fin.ext two
      subst slot
      cases recorded
    simpa only [refreshedState,ite_eq_right different] using recorded
  refine { GeneralNominalRefinements.refl twiceRevised.context.state with
    nominals := ?_
    known := ?_ }
  · intro slot d recorded
    exact retained slot _ ((GeneralNominalRefinements.refl twiceRevised.context.state).nominals slot d recorded)
  · intro source known
    obtain ⟨slot,equal,head | nominal⟩ := known
    · exact ⟨slot,equal,Or.inl head⟩
    · obtain ⟨d,recorded⟩ := nominal
      exact ⟨slot,equal,Or.inr ⟨d,retained slot d recorded⟩⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def refresh_certificate : GeneralNominalCycleSteps.Refresh twiceRevised refreshedContext where
  refines := refines
  interpretation := rfl
  exact := by
    intro m valid
    refine ⟨valid.1.1,?_,valid.1.2.2⟩
    intro slot d recorded
    change Fin 4 at slot
    change GeneralNominalState.Descriptor 4 at d
    change (if slot.val = 2 then some descriptor else twiceRevised.context.state.nominals slot) = some d at recorded
    by_cases two : slot.val = 2
    · rw [ite_eq_left two] at recorded
      have same := Option.some.inj recorded; subst d
      have index : slot = (2 : Fin 4) := Fin.ext two
      subst slot
      refine ⟨[.inl (m 2).1],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,?_⟩
      exact self_equation m (valid.2.1 packet (by simp [twiceRevised,Revision.result,regenerate,revised,installed,GeneralNominalFeedbackSites.install]))
    · rw [ite_eq_right two] at recorded
      exact valid.1.2.1 slot d recorded
  support := fun _ member => member

theorem child_known : GeneralNominalState.Known refreshedState 2 :=
  ⟨⟨2,by decide +kernel⟩,rfl,Or.inr ⟨descriptor,rfl⟩⟩

theorem source_unknown : ¬ GeneralNominalState.Known twiceRevised.context.state 2 := by
  rintro ⟨slot,same,head | ⟨observed,recorded⟩⟩
  · change slot.val = 2 at same
    have same : slot = (2 : Fin 4) := Fin.ext same
    subst slot
    exact head rfl
  · change slot.val = 2 at same
    have same : slot = (2 : Fin 4) := Fin.ext same
    subst slot
    change none = some observed at recorded
    cases recorded

noncomputable abbrev after := { pointFinish with current := refreshed }

/-- This update is enabled even after all old descriptors are point-closed. -/
theorem remaining_update : GeneralNominalSupportSteps.At registry pointFinish root after := by
  apply GeneralNominalSupportSteps.At.administrative root refreshed
  apply GeneralNominalSupportSteps.Administrative.refresh root refreshedContext refresh_certificate 2
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨(2 : Fin 4),rfl⟩
  · exact source_unknown
  · exact child_known

theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry pointFinish root := by
  intro stable
  exact stable root .root after remaining_update

/-- Complete journal models are preserved, not just one inhabited assignment. -/
theorem models_iff (m : GeneralNominalCommonBridge.Assignment) :
    Models after.current m ↔ Models pointFinish.current m :=
  GeneralNominalCycleSteps.refresh_models refresh_certificate m

theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles)
    registry root after := by
  obtain ⟨initial,started,path⟩ := point_reachable
  exact ⟨initial,started,.tail path ⟨root,.root,remaining_update⟩⟩

theorem child_linked : GeneralNominalState.Linked refreshedState child.demand := by
  constructor
  · intro index
    have supported (slot : Fin 4) : slot.val ∈ GeneralNominalState.sources refreshedState :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
    exact ⟨supported 2,supported 3⟩
  · intro o member
    have same := List.mem_singleton.mp member; subst o
    have key : GeneralNominalAllocation.origin root.identity 2 5 21 0 ∈ GeneralNominalAllocation.keys registry root.identity := by
      simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys]
    exact (GeneralNominalSourceFormation.installation_reserves packet _ key).1

theorem child_raw_K2 : GeneralNominalCycleK2.RootK2 refreshedState child.demand := by
  refine ⟨child_linked,?_,⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩,rfl,Or.inl ?_⟩
  · rintro ⟨index,unknown⟩
    exact unknown child_known
  · exact ⟨⟨2,by decide +kernel⟩,Or.inr ⟨descriptor,rfl,0,rfl⟩,.nil _⟩

theorem child_rejected : GeneralNominalFeedbackK2.Local registry refreshed child .rejected :=
  GeneralNominalFeedbackK2.root_rejected registry refreshed child (Or.inl child_raw_K2)

theorem child_never_expanded (next : Packet roles) (focus : next.site.occurrence = child) :
    ¬ GeneralNominalFeedbackSteps.Installable registry refreshed next := by
  apply GeneralNominalFeedbackSteps.rootK2_never_installed
  rw [focus]
  exact Or.inl child_raw_K2


/-- The old generated child now has an actual rejected support frontier. -/
theorem child_support_rejected : GeneralNominalSupportBoundary.Local registry after child .rejected := by
  exact .rejected ⟨GeneralNominalFeedbackK2.root_ready (Or.inl child_raw_K2),Or.inl (Or.inl child_raw_K2)⟩

theorem child_generated : Generated after.current root child := by
  apply Generated.child Generated.root
  change (root,child) ∈ [] ++ packet.children.map (fun c => (root,c))
  rw [children_exact]
  simp

/-- A concrete inhabited final snapshot with its generated child classified;
this does not claim the whole snapshot is stable. -/
theorem reached_rejected_child :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root after ∧
    Models after.current model ∧ Generated after.current root child ∧
    GeneralNominalSupportBoundary.Local registry after child .rejected :=
  ⟨reachable,(models_iff model).mpr point_models,child_generated,child_support_rejected⟩

end Yulang.GeneralDictionarySupportPointRefresh
