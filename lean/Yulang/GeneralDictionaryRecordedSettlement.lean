import Yulang.GeneralDictionarySettledRootEvidence

/-! Finite selected packet coverage gives actual I26 ledger settlement.
Coverage is explicit: semantic classification does not imply that terminal
packets were recorded. No Stable or Evidence premise is smuggled into it. -/
namespace Yulang.GeneralDictionaryRecordedSettlement
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState CommonRoleOutermostResolver
open GeneralDictionarySettledProjection
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- Recorded occurrence and exact child list at each selected descendant.
This is a journal coverage hypothesis, not a consequence of general reachability. -/
def PacketCoverage (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ child, B4Target.Steps (fun parent child => Child
    (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child →
    ∀ key children, B4TargetV3.Local (fresh roles).toSourceBoundary registry state child
      (.selected key children) → ∃ packet ∈ state.current.packets,
        packet.site.occurrence = child ∧ packet.children = children

theorem coverage_child {root child : Occurrence roles}
    (coverage : PacketCoverage registry state root)
    (edge : Child (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child root) :
    PacketCoverage registry state child := by
  intro descendant path
  apply coverage descendant
  induction path with
  | refl => exact .tail .refl edge
  | tail _ next ih => exact .tail ih next

mutual
  /-- Classification plus actual finite packet coverage, not classification alone. -/
  theorem classified_discharged (root : Occurrence roles) (dictionary : Dictionary)
      (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
      (coverage : PacketCoverage registry state root) : Discharged state.current root := by
    match dictionary, classified with
    | .node key dictionaries, .selected safe unique all =>
      have localRule : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root
          (.selected key _) := .selected safe unique
      obtain ⟨packet,member,site,children⟩ := coverage root .refl _ _ localRule
      rw [← site]
      apply Discharged.packet packet member
      rw [children]
      exact children_discharged dictionaries _ all
        (fun child member => coverage_child coverage ⟨_,_,localRule,member⟩)
  termination_by sizeOf dictionary

  theorem children_discharged (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (classified : All₂ (fun root dictionary => B4TargetV3.Classify
        (fresh roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries)
      (coverage : ∀ child ∈ roots, PacketCoverage registry state child) :
      ∀ child ∈ roots, Discharged state.current child := by
    cases classified with
    | nil => intro child member; cases member
    | cons first rest =>
      intro child member
      rcases List.mem_cons.mp member with rfl | member
      · exact classified_discharged _ _ first (coverage _ (by simp))
      · exact children_discharged _ _ rest (fun c h => coverage c (by simp [h])) child member
  termination_by sizeOf dictionaries
end

theorem completed_discharged {root : Occurrence roles} {tree : Tree} {dictionary : Dictionary}
    (resolved : Resolves (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) root tree)
    (completed : B4TargetV3.Completed tree (.selected dictionary))
    (coverage : PacketCoverage registry state root) : Discharged state.current root :=
  classified_discharged root dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed) coverage

/-- A recorded parent packet is settled once its finite selected child
dictionaries have coverage. No discharge premise is required. -/
theorem packet_settled {packet : Packet roles} {dictionaries : List Dictionary}
    (member : packet ∈ state.current.packets)
    (classified : All₂ (fun root dictionary => B4TargetV3.Classify
      (fresh roles).toSourceBoundary registry state root (.selected dictionary)) packet.children dictionaries)
    (coverage : ∀ child ∈ packet.children, PacketCoverage registry state child) :
    GeneralNominalSettledSupport.PacketSettled state.current packet :=
  ⟨member,children_discharged dictionaries packet.children classified coverage⟩

theorem output_trusted {packet : Packet roles} {dictionaries : List Dictionary}
    {facts : List (Fact roles)} {support : List (Occurrence roles)}
    (trusted : GeneralNominalSettledSupport.Trusted state facts)
    (output : Fact.outputs packet support ∈ state.facts)
    (input : Fact.inputs packet support ∈ facts)
    (member : packet ∈ state.current.packets)
    (classified : All₂ (fun root dictionary => B4TargetV3.Classify
      (fresh roles).toSourceBoundary registry state root (.selected dictionary)) packet.children dictionaries)
    (coverage : ∀ child ∈ packet.children, PacketCoverage registry state child) :
    GeneralNominalSettledSupport.Trusted state (Fact.outputs packet support :: facts) :=
  .output packet support trusted output input (packet_settled member classified coverage)
end Yulang.GeneralDictionaryRecordedSettlement
