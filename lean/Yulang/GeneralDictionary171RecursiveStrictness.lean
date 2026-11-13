import Yulang.GeneralDictionary171SpineExample
import Yulang.GeneralDictionary170NamedSelection

/-! Recursive strictness, not just a new isolated leaf. The parent theorem
retains a recorded packet and an actual model/selection as premises; it does
not manufacture a reachable nonterminal execution. -/
namespace Yulang.GeneralDictionary171RecursiveStrictness
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback
open CommonRoleOutermostResolver (All₂)
open GeneralDictionary169NamedTree (NamedTree)
variable {roles : Roles.RoleDecls}

private theorem mixed_nodes (tree : GeneralDictionaryMixed168Tree.MixedTree registry state focus payload) :
    Nonempty (GeneralDictionary170NamedCoverage.Node registry state focus) := by
  cases tree with
  | recorded packet member relocation payloads children => exact ⟨.recorded packet member relocation⟩
  | scalar focus declaration visible checked shape => exact ⟨.scalar focus declaration visible checked shape⟩
  | spine focus declaration visible checked shape => exact ⟨.spine focus declaration visible checked shape⟩

theorem old_tree_node (tree : NamedTree registry state focus payload) :
    Nonempty (GeneralDictionary170NamedCoverage.Node registry state focus) := by
  cases tree with
  | mixed old => exact mixed_nodes old
  | recorded packet member relocation payloads children => exact ⟨.recorded packet member relocation⟩
  | named focus declaration visible checked shape => exact ⟨.named focus declaration visible checked shape⟩

private theorem lift_mixed (children : All₂
    (GeneralDictionaryMixed168Tree.MixedTree registry state) sites payloads) :
    All₂ (NamedTree registry state) sites payloads := by
  induction children with
  | nil => exact .nil
  | cons one rest ih => exact .cons (.mixed one) ih

/-- Structural decomposition retains old child certificates, rather than only
returning their semantic interpretation. -/
theorem old_tree_decompose (tree : NamedTree registry state focus (.node key payloads)) :
    ∃ node : GeneralDictionary170NamedCoverage.Node registry state focus,
      node.key = key ∧ All₂ (NamedTree registry state) node.children payloads := by
  cases tree with
  | mixed old =>
    cases old with
    | recorded packet member relocation payloads children =>
      exact ⟨.recorded packet member relocation,rfl,lift_mixed children⟩
    | scalar focus declaration visible checked shape =>
      exact ⟨.scalar focus declaration visible checked shape,rfl,.nil⟩
    | spine focus declaration visible checked shape =>
      exact ⟨.spine focus declaration visible checked shape,rfl,.nil⟩
  | recorded packet member relocation payloads children =>
    exact ⟨.recorded packet member relocation,rfl,children⟩
  | named focus declaration visible checked shape =>
    exact ⟨.named focus declaration visible checked shape,rfl,.nil⟩

private theorem old_node_instance {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (node : GeneralDictionary170NamedCoverage.Node registry state focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus node.key node.children := by
  have metadata := GeneralDictionarySharedMetadata.formed_metadata formed
  cases node with
  | recorded packet member relocation =>
    exact GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid
  | scalar focus declaration visible checked shape =>
    exact GeneralDictionaryScalarLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1
  | spine focus declaration visible checked shape =>
    exact GeneralDictionarySpineLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1
  | named focus declaration visible checked shape =>
    exact GeneralDictionary169NamedLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1

/-- Same-current-model selection fixes literal child order even in the old
structural syntax. No completeness or arbitrary model existence is inferred. -/
theorem old_tree_selected_children {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : NamedTree registry state focus (.node key payloads))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current focus (.selected chosen children)) :
    key = chosen ∧ All₂ (NamedTree registry state) children payloads := by
  obtain ⟨node,equal,descendants⟩ := old_tree_decompose tree
  obtain ⟨sameKey,sameChildren⟩ := GeneralDictionarySelectedInstanceCoherence.instance_selected
    registry state.current focus model node.key chosen node.children children
      (old_node_instance formed node model valid) selected
  exact ⟨equal.symm.trans sameKey,sameChildren ▸ descendants⟩

private theorem all_member (children : All₂ (NamedTree registry state) sites payloads)
    (member : child ∈ sites) : ∃ payload, NamedTree registry state child payload := by
  induction children with
  | nil => cases member
  | cons one rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst child; exact ⟨_,one⟩
    · exact ih member

/-- An old local-node obstruction at any selected child propagates to the
parent's whole old recursive dictionary, at every payload. -/
theorem child_gap_propagates {registry : Registry} {state : Tracked roles} {root focus child : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current focus (.selected chosen children))
    (member : child ∈ children)
    (gap : ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry state child)) :
    ∀ payload, ¬ NamedTree registry state focus payload := by
  intro payload tree
  cases payload with
  | node key payloads =>
    have descendants := (old_tree_selected_children formed tree model valid selected).2
    obtain ⟨_,one⟩ := all_member descendants member
    exact gap (old_tree_node one)

/-- Generic nonterminal graft. Actual packet membership/relocation, exact one
child, and an inhabited current model/selection are explicit assumptions. The
new recursive certificate exists while no old certificate can exist. This is
not an assertion that these parent premises hold for the initial leaf fixture. -/
theorem recorded_parent_strict {registry : Registry} {state : Tracked roles} {root child : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet)
    (oneChild : packet.children = [child])
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionary170NamedSpine.Shape registry state.current.context child declaration checked)
    (gap : ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry state child))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current packet.site.occurrence
      (.selected packet.declaration.id packet.children)) :
    GeneralDictionary171SpineTree.Tree registry state packet.site.occurrence
      (.node packet.declaration.id [.node declaration.id []]) ∧
    (∀ payload, ¬ NamedTree registry state packet.site.occurrence payload) ∧
    (∀ assignment, Models state.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context assignment packet.site.occurrence
        (.node packet.declaration.id [.node declaration.id []])) := by
  have children : All₂ (GeneralDictionary171SpineTree.Tree registry state) packet.children
      [.node declaration.id []] := by
    rw [oneChild]
    exact .cons (.namedSpine child declaration visible checked shape) .nil
  have tree := GeneralDictionary171SpineTree.Tree.recorded packet member relocation _ children
  exact ⟨tree,child_gap_propagates formed model valid selected (by rw [oneChild]; exact List.mem_singleton_self _) gap,
    fun assignment valid => GeneralDictionary171SpineTree.current_evidence formed tree assignment valid⟩

open GeneralDictionary170NamedSpineExample in
theorem actual_no_old_tree (payload : Payload) : ¬ NamedTree registry start root payload :=
  fun tree => no_current_local_node (old_tree_node tree)
end Yulang.GeneralDictionary171RecursiveStrictness
