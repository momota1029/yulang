import Yulang.GeneralDictionaryCenteredRecorded176

/-! Every actual centered history preserves exact packet-ledger correspondence.
Original-context source evidence is paired with the actual center equations.
No claim identifies original and current inspection contexts. -/
namespace Yulang.GeneralDictionaryCenteredLedger176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenters GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def ExactLedger (state : State roles) : Prop :=
  state.plans.map Plan.packet = state.erased.current.packets

theorem exact_at (prior : ExactLedger before) (action : At registry before focus after) :
    ExactLedger after := by
  cases action with
  | administrative focus after action => cases action <;> exact prior
  | refresh | merge => exact prior
  | install plan support enabled novel guard =>
    change plan.packet :: before.plans.map Plan.packet = plan.packet :: before.erased.current.packets
    exact congrArg (List.cons plan.packet) prior

theorem exact_trace (prior : ExactLedger before)
    (path : B4Target.Steps (Step registry root) before after) : ExactLedger after := by
  induction path with
  | refl => exact prior
  | tail path step ih => exact exact_at ih step.choose_spec.2

theorem initial_exact (context : GeneralNominalCandidates.Context) :
    ExactLedger (initial context root) := rfl

theorem reachable_exact
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state) : ExactLedger state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact exact_trace (initial_exact context) path

theorem packet_member (ledger : ExactLedger state) (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet ∈ state.erased.current.packets := by
  rw [← ledger]
  exact List.mem_map.mpr ⟨plan,member,rfl⟩

theorem packet_has_plan (ledger : ExactLedger state)
    (packet : GeneralNominalSaturationState.Packet roles)
    (member : packet ∈ state.erased.current.packets) :
    ∃ plan ∈ state.plans, plan.packet = packet := by
  rw [← ledger] at member
  exact List.mem_map.mp member

theorem plan_instance
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans)
    (model : Assignment) (valid : Models state model) :
    Instance registry plan.packet.context model plan.packet.site.occurrence
      plan.packet.declaration.id plan.packet.children ∧ plan.Equations model :=
  ⟨GeneralDictionaryCenteredRecorded176.reachable_stored_instance reachable plan.packet
    (packet_member (reachable_exact reachable) plan member) model valid,
    valid.2.2 plan member⟩

theorem plan_evidence
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans)
    (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry plan.packet.context model) plan.packet.children dictionaries) :
    Evidence registry plan.packet.context model plan.packet.site.occurrence
      (.node plan.packet.declaration.id dictionaries) ∧ plan.Equations model :=
  ⟨evidence_node _ _ _ _ _ _ _ (plan_instance reachable plan member model valid).1 children,
    (plan_instance reachable plan member model valid).2⟩

end Yulang.GeneralDictionaryCenteredLedger176
