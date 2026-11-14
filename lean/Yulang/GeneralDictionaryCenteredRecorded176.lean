import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralDictionarySharedRecordedEvidence

/-! Source instances through every actual centered action. Stored inspection
contexts are explicit. This is not a theorem that current inspection is unchanged. -/
namespace Yulang.GeneralDictionaryCenteredRecorded176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence
open GeneralNominalSaturationState (Packet Generated)
open GeneralDictionarySharedRecordedEvidence (Metadata)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def Recorded (registry : Registry) (state : State roles) : Prop :=
  ∀ packet ∈ state.erased.current.packets, Metadata registry packet ∧
    ∀ child ∈ packet.children, (packet.site.occurrence,child) ∈ state.erased.current.edges

theorem recorded_at (prior : Recorded registry before) (action : At registry before focus after) :
    Recorded registry after := by
  cases action with
  | administrative focus after action =>
    have packets : after.packets = before.erased.current.packets := by cases action <;> rfl
    have edges : after.edges = before.erased.current.edges := by cases action <;> rfl
    intro packet member
    simpa only [administrative,packets,edges] using prior packet (packets ▸ member)
  | refresh | merge => exact prior
  | install plan support enabled novel guard =>
    intro packet member
    change packet ∈ plan.packet :: before.erased.current.packets at member
    rcases List.mem_cons.mp member with same | old
    · subst packet
      refine ⟨⟨enabled.1.1,?_,enabled.1.2.2.2.2.1,enabled.1.2.2.2.2.2.1,
        enabled.1.2.2.2.2.2.2.1⟩,?_⟩
      · simpa only [enabled.1.1] using enabled.1.2.2.2.1
      · intro child present
        exact List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩)
    · obtain ⟨metadata,edges⟩ := prior packet old
      exact ⟨metadata,fun child present => List.mem_append_left _ (edges child present)⟩

theorem recorded_trace (prior : Recorded registry before)
    (path : B4Target.Steps (Step registry root) before after) : Recorded registry after := by
  induction path with
  | refl => exact prior
  | tail path step ih => exact recorded_at ih step.choose_spec.2

theorem initial_recorded (context : GeneralNominalCandidates.Context) :
    Recorded registry (initial context root) := by
  intro packet member
  cases member

theorem reachable_recorded
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state) : Recorded registry state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact recorded_trace (initial_recorded context) path

theorem recorded_committed (recorded : Recorded registry state)
    (packet : Packet roles) (member : packet ∈ state.erased.current.packets) :
    GeneralNominalFeedbackSteps.Committed state.erased.current packet :=
  ⟨fun _ valid => valid.2.1 packet member,(recorded packet member).2⟩

theorem stored_instance (recorded : Recorded registry state)
    (packet : Packet roles) (member : packet ∈ state.erased.current.packets)
    (model : Assignment) (valid : Models state model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children := by
  obtain ⟨same,visible,role,located,prepared⟩ := (recorded packet member).1
  have result := GeneralDictionaryCommittedEvidence.committed_instance state.erased.current packet
    visible role located prepared (recorded_committed recorded packet member) model valid.1
  simpa only [same] using result

theorem reachable_stored_instance
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (packet : Packet roles) (member : packet ∈ state.erased.current.packets)
    (model : Assignment) (valid : Models state model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children :=
  stored_instance (reachable_recorded reachable) packet member model valid

theorem stored_evidence (recorded : Recorded registry state)
    (packet : Packet roles) (member : packet ∈ state.erased.current.packets)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry packet.context model) packet.children dictionaries) :
    Evidence registry packet.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (stored_instance recorded packet member model valid) children

theorem current_instance (recorded : Recorded registry state)
    (packet : Packet roles) (member : packet ∈ state.erased.current.packets)
    (extension : GeneralDictionaryOrdinaryTrace.Extension packet.context state.erased.current.context)
    (model : Assignment) (valid : Models state model) :
    Instance registry state.erased.current.context model packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ extension model valid.1.1 _ _ _
    (stored_instance recorded packet member model valid)

end Yulang.GeneralDictionaryCenteredRecorded176
