import Yulang.GeneralNominalCenteredCommitment

/-! Selection constructs an exact current-context packet before any production
assumption. A single existential completion supplies the remaining joint,
value-support, and common-model obligations for that packet. -/
namespace Yulang.GeneralNominalCenteredSelectedCompletion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalSaturationState (Generated Packet)

variable {roles : Roles.RoleDecls}

structure Frame (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (plan : Plan roles) : Prop where
  registry_eq : plan.packet.registry = registry
  context_eq : plan.packet.context = state.erased.current.context
  occurrence_eq : plan.packet.site.occurrence = focus
  key_eq : plan.packet.declaration.id = key
  children_eq : plan.packet.children = children
  raw_recorded : plan.packet.site ∈ state.erased.current.sites
  center_recorded : plan.input ∈ state.sites
  visible : plan.packet.declaration ∈ registry.declarations
  role_eq : plan.packet.declaration.role = focus.demand.role
  located : GeneralNominalRecursiveCandidates.arguments plan.packet.context focus = some plan.packet.bounds
  prepared : GeneralNominalRecursiveCandidates.Prepared plan.packet.registry plan.packet.context focus plan.packet.declaration plan.packet.checked

theorem selected_frame
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    ∃ plan, Frame registry state focus key children plan := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  obtain ⟨raw,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
  obtain ⟨center,recorded,centerSame⟩ := GeneralNominalCenteredTrace.raw_site_centered path raw member
  have old := selected_old selected
  cases old with
  | selected safe unique =>
    obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,kids⟩ := unique.1
    let packet : Packet roles := ⟨registry,state.erased.current.context,raw,declaration,checked,bounds⟩
    let plan : Plan roles := ⟨packet,center,centerSame⟩
    refine ⟨plan,rfl,rfl,same,identity,?_,member,recorded,visible,role,located,prepared⟩
    change GeneralNominalAllocation.children _ registry raw.occurrence declaration checked _ = children
    rw [same]
    exact kids.symm

def Completion (registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  GeneralNominalJointCandidates.Joint registry state.erased.current plan.packet.site.occurrence plan.packet.declaration.id ∧
    ∃ support, GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
      ∃ model, Models state model ∧ plan.Holds model

theorem frame_installable_iff (selected : Local registry state focus (.selected key children))
    (frame : Frame registry state focus key children plan) :
    GeneralNominalCenteredBoundary.Installable registry state plan ↔ Completion registry state plan := by
  constructor
  · intro enabled
    refine ⟨enabled.1.1.2.2.2.2.2.2.2.2.2.2.2,?_⟩
    have old := selected_old selected
    rw [← frame.occurrence_eq] at old
    exact (GeneralNominalCenteredInspection.selected_installable_iff plan old enabled.1 frame.center_recorded).mp enabled
  · rintro ⟨joint,support,values,model,valid,holds⟩
    have old := GeneralNominalCenteredSelection.selected_feedback (selected_old selected)
    have chosen : GeneralNominalFeedbackK2.Local registry state.erased.current plan.packet.site.occurrence
        (.selected plan.packet.declaration.id plan.packet.children) := by
      rw [frame.occurrence_eq,frame.key_eq,frame.children_eq]; exact old
    have closed := (selected_ready selected).2.1 plan.packet.site frame.raw_recorded frame.occurrence_eq
    have base : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet := by
      refine ⟨⟨frame.registry_eq,frame.context_eq,frame.raw_recorded,frame.visible,?_,?_,?_,
        GeneralNominalFeedbackK2.selected_legacy chosen,?_,?_,⟨model,valid.1,holds.1⟩,joint⟩,chosen,closed⟩
      · simpa only [frame.occurrence_eq] using frame.role_eq
      · simpa only [frame.occurrence_eq] using frame.located
      · simpa only [frame.occurrence_eq] using frame.prepared
      · intro prior present alias
        exact (joint.1 prior present alias).symm
      · intro other present same
        exact closed other present (GeneralDictionaryFeedbackEvidence.sameInputs_recovered _ _ _ same)
    have old := selected_old selected
    rw [← frame.occurrence_eq] at old
    exact (GeneralNominalCenteredInspection.selected_installable_iff plan old base frame.center_recorded).mpr
      ⟨support,values,model,valid,holds⟩

theorem stable_completed_committed
    (selected : Local registry state focus (.selected key children))
    (stable : Stable registry state focus) (frame : Frame registry state focus key children plan)
    (completion : Completion registry state plan) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet :=
  GeneralNominalCenteredSelection.stable_committed stable plan frame.occurrence_eq
    ((frame_installable_iff selected frame).mpr completion)

theorem stable_uncommitted_obstruction
    (selected : Local registry state focus (.selected key children))
    (stable : Stable registry state focus) (frame : Frame registry state focus key children plan)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet) :
    ¬ GeneralNominalJointCandidates.Joint registry state.erased.current plan.packet.site.occurrence plan.packet.declaration.id ∨
    (∀ support, ¬ GeneralNominalValueSupport.PacketGuard state.erased plan.packet support) ∨
    ¬ ∃ model, Models state model ∧ plan.Holds model := by
  classical
  by_cases joint : GeneralNominalJointCandidates.Joint registry state.erased.current plan.packet.site.occurrence plan.packet.declaration.id
  · by_cases supported : ∃ support, GeneralNominalValueSupport.PacketGuard state.erased plan.packet support
    · refine Or.inr (Or.inr ?_)
      intro feasible
      obtain ⟨support,values⟩ := supported
      exact novel (stable_completed_committed selected stable frame ⟨joint,support,values,feasible⟩)
    · exact Or.inr (Or.inl (fun support values => supported ⟨support,values⟩))
  · exact Or.inl joint

theorem stable_selected_commitment_or_obstruction
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (stable : Stable registry state focus) (selected : Local registry state focus (.selected key children)) :
    ∃ plan, Frame registry state focus key children plan ∧
      (GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet ∨
       ¬ GeneralNominalJointCandidates.Joint registry state.erased.current plan.packet.site.occurrence plan.packet.declaration.id ∨
       (∀ support, ¬ GeneralNominalValueSupport.PacketGuard state.erased plan.packet support) ∨
       ¬ ∃ model, Models state model ∧ plan.Holds model) := by
  classical
  obtain ⟨plan,frame⟩ := selected_frame reachable generated selected
  refine ⟨plan,frame,?_⟩
  by_cases committed : GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet
  · exact Or.inl committed
  · exact Or.inr (stable_uncommitted_obstruction selected stable frame committed)

/-- One exact packet, one support certificate, and one common model suffice.
No branch completion is required for leaf nodes or already committed nodes. -/
def UncoveredCompletion (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV5.Reachable (boundary roles) registry root state →
    Generated state.erased.current root focus → Stable registry state focus →
    Local registry state focus (.selected key children) → children ≠ [] →
    (¬ ∃ plan, Frame registry state focus key children plan ∧
      GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet) →
    ∃ plan, Frame registry state focus key children plan ∧ Completion registry state plan

theorem stable_selected_committed (complete : UncoveredCompletion roles)
    (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (stable : Stable registry state focus) (selected : Local registry state focus (.selected key children))
    (nonempty : children ≠ []) :
    ∃ plan, Frame registry state focus key children plan ∧
      GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  apply Classical.byContradiction
  intro missing
  obtain ⟨plan,frame,completion⟩ := complete registry checked state root focus key children
    reachable generated stable selected nonempty missing
  exact missing ⟨plan,frame,stable_completed_committed selected stable frame completion⟩

theorem generatedChildren (complete : UncoveredCompletion roles) : B4SkeletonV5.GeneratedChildren (boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.erased.current root focus := by
    rcases reached with rfl | given
    · exact .root
    · exact given
  have selected := (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
  have nonempty : children ≠ [] := by intro empty; simp [empty] at member
  obtain ⟨plan,frame,committed⟩ := stable_selected_committed complete checked reachable generated stable selected nonempty
  apply Generated.child generated
  rw [← frame.occurrence_eq]
  exact committed.2 child (frame.children_eq ▸ member)

theorem production_completes (production : GeneralNominalCenteredAdministrativeProduction.ReachableProduction roles) :
    UncoveredCompletion roles := by
  intro registry checked state root focus key children reachable generated stable selected nonempty missing
  have supplied := production registry checked state root focus key children reachable generated stable selected nonempty
  obtain ⟨plan,frame⟩ := selected_frame reachable generated selected
  obtain ⟨other,same,identity,kids,recorded,enabled⟩ :=
    GeneralNominalCenteredAdministrativeProduction.selected_base_plan reachable generated selected supplied.1
  have frameOther : Frame registry state focus key children other :=
    ⟨enabled.1.1,enabled.1.2.1,same,identity,kids,enabled.1.2.2.1,recorded,enabled.1.2.2.2.1,
      by simpa only [same] using enabled.1.2.2.2.2.1,
      by simpa only [same] using enabled.1.2.2.2.2.2.1,
      by simpa only [same] using enabled.1.2.2.2.2.2.2.1⟩
  refine ⟨other,frameOther,?_,supplied.2 other same identity recorded enabled⟩
  simpa only [same,identity] using supplied.1

end Yulang.GeneralNominalCenteredSelectedCompletion
