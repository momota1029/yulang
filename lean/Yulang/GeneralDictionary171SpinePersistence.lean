import Yulang.GeneralDictionary171SpineAccessible
import Yulang.GeneralDictionary171NamedSpinePersistence
import Yulang.GeneralDictionary170NamedCoveragePersistence

/-! Ordinary context growth transports the chosen local coverage itself,
preserving the same domain, child edges and declaration keys. It does not
create coverage from a stable state and excludes descriptor refresh. -/
namespace Yulang.GeneralDictionary171SpinePersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionary171SpineCoverage
variable {roles : Roles.RoleDecls}

theorem tree_extension {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (certificate : GeneralDictionary171SpineTree.Tree registry before occurrence payload) :
    GeneralDictionary171SpineTree.Tree registry after occurrence payload := by
  induction certificate using GeneralDictionary171SpineTree.Tree.rec
    (motive_2 := fun sites payloads _ => CommonRoleOutermostResolver.All₂
      (GeneralDictionary171SpineTree.Tree registry after) sites payloads) with
  | old previous => exact .old (GeneralDictionary169NamedPersistence.extension members growth previous)
  | recorded packet member relocation payloads children ih =>
    exact .recorded packet (members packet member)
      (GeneralDictionary169RelocationComposition.packet_extension registry before after packet relocation growth) payloads ih
  | namedSpine occurrence declaration visible checked shape =>
    obtain ⟨next⟩ := GeneralDictionary171NamedSpinePersistence.extension growth shape
    exact .namedSpine occurrence declaration visible checked next
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem tree_ordinary_steps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (certificate : GeneralDictionary171SpineTree.Tree registry before occurrence payload) :
    GeneralDictionary171SpineTree.Tree registry after occurrence payload :=
  tree_extension (GeneralDictionary169MixedPersistence.packets_steps
      (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path))
    (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) certificate

theorem node_transport {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    {occurrence : Occurrence roles} (node : Node registry before occurrence) :
    ∃ next : Node registry after occurrence,
      next.children = node.children ∧ next.key = node.key := by
  cases node with
  | old previous =>
    obtain ⟨next,children,key⟩ := GeneralDictionary170NamedCoveragePersistence.node_transport members growth previous
    exact ⟨.old next,children,key⟩
  | namedSpine declaration visible checked shape =>
    obtain ⟨next⟩ := GeneralDictionary171NamedSpinePersistence.extension growth shape
    exact ⟨.namedSpine occurrence declaration visible checked next,rfl,rfl⟩

noncomputable def nodeExtension {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    {occurrence : Occurrence roles} (node : Node registry before occurrence) :
    Node registry after occurrence := Classical.choose (node_transport members growth node)

theorem node_children {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    {occurrence : Occurrence roles} (node : Node registry before occurrence) :
    (nodeExtension members growth node).children = node.children :=
  (Classical.choose_spec (node_transport members growth node)).1

theorem node_key {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    {occurrence : Occurrence roles} (node : Node registry before occurrence) :
    (nodeExtension members growth node).key = node.key :=
  (Classical.choose_spec (node_transport members growth node)).2

noncomputable def extension {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (coverage : Coverage registry before domain) : Coverage registry after domain where
  node := fun occurrence present => nodeExtension members growth (coverage.node occurrence present)
  closed := by
    intro occurrence present child member
    rw [node_children] at member
    exact coverage.closed occurrence present child member

theorem child_iff {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (coverage : Coverage registry before domain) (child parent : Subtype domain) :
    Child (extension members growth coverage) child parent ↔ Child coverage child parent := by
  unfold Child extension
  rw [node_children]

noncomputable def ordinarySteps {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) : Coverage registry after domain :=
  extension (GeneralDictionary169MixedPersistence.packets_steps
      (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path))
    (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) coverage

theorem ordinary_children {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) (child parent : Subtype domain) :
    Child (ordinarySteps path coverage) child parent ↔ Child coverage child parent :=
  child_iff _ _ _ _ _

theorem ordinary_dictionary {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) (focus : Subtype domain)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root after) :
    ∃ payload, GeneralDictionary171SpineTree.Tree registry after focus.val payload ∧
      ∀ model, Models after.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus.val payload :=
  GeneralDictionary171SpineAccessible.covered_dictionary (ordinarySteps path coverage) focus formed

/-- Choose one payload before the continuation. Its finite certificate survives
and is interpreted in every final model, with no initial model assumption. -/
theorem ordinary_uniform_payload {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) (focus : Subtype domain)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root after) :
    ∃ payload, GeneralDictionary171SpineTree.Tree registry before focus.val payload ∧
      GeneralDictionary171SpineTree.Tree registry after focus.val payload ∧
      ∀ model, Models after.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus.val payload := by
  obtain ⟨payload,tree⟩ := GeneralDictionary171SpineAccessible.covered_tree coverage focus
  have next := tree_ordinary_steps path tree
  exact ⟨payload,tree,next,fun model valid => GeneralDictionary171SpineTree.current_evidence formed next model valid⟩
end Yulang.GeneralDictionary171SpinePersistence
