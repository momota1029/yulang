import Yulang.GeneralDictionary171SpineCoverage
import Yulang.GeneralDictionary169CoverageAccessible

/-! A fixed finite journal bounds every nonleaf certificate node. Literal
child identities strictly increase, so a reverse bounded numeric rank proves
accessibility of the chosen dictionary graph. This does not bound execution. -/
namespace Yulang.GeneralDictionary171SpineAccessible
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionary171SpineCoverage
variable {roles : Roles.RoleDecls}

private theorem member_max (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def ceiling (state : Tracked roles) : Nat :=
  (state.current.packets.map fun packet => packet.site.occurrence.identity).foldr max 0

private theorem node_edge {registry : Registry} {state : Tracked roles} {occurrence : Occurrence roles}
    (node : Node registry state occurrence) (child : Occurrence roles) (member : child ∈ node.children) :
    occurrence.identity ≤ ceiling state ∧ occurrence.identity < child.identity := by
  cases node with
  | old previous =>
    cases previous with
    | recorded packet recorded relocation =>
      exact ⟨member_max _ _ (List.mem_map.mpr ⟨packet,recorded,rfl⟩),GeneralDictionary169CoverageAccessible.packet_child_above packet child member⟩
    | scalar occurrence declaration visible checked shape => cases member
    | spine occurrence declaration visible checked shape => cases member
    | named occurrence declaration visible checked shape => cases member
  | namedSpine declaration visible checked shape => cases member

def rank (state : Tracked roles) (occurrence : Occurrence roles) : Nat :=
  ceiling state + 1 - occurrence.identity

theorem child_rank {registry : Registry} {state : Tracked roles} {domain : Occurrence roles → Prop}
    (coverage : Coverage registry state domain) (child parent : Subtype domain)
    (edge : Child coverage child parent) : rank state child.val < rank state parent.val := by
  have bounds := node_edge (coverage.node parent.val parent.property) child.val edge
  unfold rank
  omega

theorem coverage_accessible {registry : Registry} {state : Tracked roles} {domain : Occurrence roles → Prop}
    (coverage : Coverage registry state domain) (focus : Subtype domain) : Acc (Child coverage) focus := by
  have all : ∀ n, ∀ current : Subtype domain, rank state current.val = n → Acc (Child coverage) current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro current equal
      constructor
      intro child edge
      apply ih (rank state child.val)
      · have smaller := child_rank coverage child current edge
        omega
      · rfl
  exact all (rank state focus.val) focus rfl

theorem covered_tree {registry : Registry} {state : Tracked roles} {domain : Occurrence roles → Prop}
    (coverage : Coverage registry state domain) (focus : Subtype domain) :
    ∃ payload, GeneralDictionary171SpineTree.Tree registry state focus.val payload :=
  accessible_tree coverage focus (coverage_accessible coverage focus)

theorem covered_dictionary {registry : Registry} {state : Tracked roles} {domain : Occurrence roles → Prop}
    (coverage : Coverage registry state domain) (focus : Subtype domain)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    ∃ payload, GeneralDictionary171SpineTree.Tree registry state focus.val payload ∧
      ∀ model, Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus.val payload :=
  uniform_dictionary coverage focus (coverage_accessible coverage focus) formed

end Yulang.GeneralDictionary171SpineAccessible
