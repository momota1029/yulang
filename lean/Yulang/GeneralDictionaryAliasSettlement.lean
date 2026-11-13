import Yulang.GeneralDictionaryRecordedSettlement

/-! I20 aliases may reuse an already recorded finite settlement tree.
The matching certificate is structural journal membership plus an actual Alias;
no Discharged or Evidence assumption occurs in coverage. -/
namespace Yulang.GeneralDictionaryAliasSettlement
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState CommonRoleOutermostResolver
open GeneralDictionarySettledProjection
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- A matching recorded packet may sit at the requested occurrence itself or
at an explicitly recorded alias site. Exact packet children are preserved. -/
def RecordedNode (state : Tracked roles) (root : Occurrence roles)
    (children : List (Occurrence roles)) : Prop :=
  ∃ packet ∈ state.current.packets, packet.children = children ∧
    (packet.site.occurrence = root ∨
      ∃ site ∈ state.current.sites, site.occurrence = root ∧
        packet.site ∈ state.current.sites ∧
        Alias state.current packet.site.occurrence.identity site.occurrence.identity)

def AliasCoverage (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ child, B4Target.Steps (fun parent child => Child
    (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child →
    ∀ key children, B4TargetV3.Local (fresh roles).toSourceBoundary registry state child
      (.selected key children) → RecordedNode state child children

theorem exact_coverage (given : GeneralDictionaryRecordedSettlement.PacketCoverage registry state root) :
    AliasCoverage registry state root := by
  intro child path key children selected
  obtain ⟨packet,member,site,kids⟩ := given child path key children selected
  exact ⟨packet,member,kids,Or.inl site⟩

theorem node_discharged (node : RecordedNode state root children)
    (done : ∀ child ∈ children, Discharged state.current child) : Discharged state.current root := by
  obtain ⟨packet,member,kids,same | aliased⟩ := node
  · rw [← same]
    exact .packet packet member (by rw [kids]; exact done)
  · obtain ⟨site,present,same,prior,alias⟩ := aliased
    rw [← same]
    exact .alias packet.site site prior present alias
      (.packet packet member (by rw [kids]; exact done))

theorem coverage_child {root child : Occurrence roles}
    (coverage : AliasCoverage registry state root)
    (edge : Child (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child root) :
    AliasCoverage registry state child := by
  intro descendant path
  apply coverage descendant
  induction path with
  | refl => exact .tail .refl edge
  | tail _ next ih => exact .tail ih next

mutual
  theorem classified_discharged (root : Occurrence roles) (dictionary : Dictionary)
      (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
      (coverage : AliasCoverage registry state root) : Discharged state.current root := by
    match dictionary, classified with
    | .node key dictionaries, .selected safe unique all =>
      have localRule : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root
          (.selected key _) := .selected safe unique
      exact node_discharged (coverage root .refl _ _ localRule)
        (children_discharged dictionaries _ all
          (fun child member => coverage_child coverage ⟨_,_,localRule,member⟩))
  termination_by sizeOf dictionary

  theorem children_discharged (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (classified : All₂ (fun root dictionary => B4TargetV3.Classify
        (fresh roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries)
      (coverage : ∀ child ∈ roots, AliasCoverage registry state child) :
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
    (coverage : AliasCoverage registry state root) : Discharged state.current root :=
  classified_discharged root dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed) coverage

theorem packet_settled {packet : Packet roles} {dictionaries : List Dictionary}
    (member : packet ∈ state.current.packets)
    (classified : All₂ (fun root dictionary => B4TargetV3.Classify
      (fresh roles).toSourceBoundary registry state root (.selected dictionary)) packet.children dictionaries)
    (coverage : ∀ child ∈ packet.children, AliasCoverage registry state child) :
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
    (coverage : ∀ child ∈ packet.children, AliasCoverage registry state child) :
    GeneralNominalSettledSupport.Trusted state (Fact.outputs packet support :: facts) :=
  .output packet support trusted output input (packet_settled member classified coverage)
end Yulang.GeneralDictionaryAliasSettlement
