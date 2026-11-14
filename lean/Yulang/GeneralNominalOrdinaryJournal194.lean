import Yulang.GeneralNominalSemanticNode194
import Yulang.GeneralDictionaryJournalTree

/-! Readback of the actual WF journal after ordinary-only execution. Neither a
Build certificate nor a final Installable premise is needed. Descriptor-changing
refresh is excluded by the explicit ordinary trace hypothesis. -/
namespace Yulang.GeneralNominalOrdinaryJournal194
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOrdinaryEvidence191
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Every packet that actually reaches the journal is a current semantic instance
for each final assignment. Installation facts are recovered from the trace, not
passed as an extra readback premise. -/
theorem packet_instance {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) after)
    (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : packet ∈ after.core.erased.current.packets)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  induction path with
  | refl => cases recorded
  | @tail before after path action ih =>
    have prior (member : packet ∈ before.core.erased.current.packets) :=
      GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ action.2 model valid.1.1.1
        packet.site.occurrence packet.declaration.id packet.children
        (ih member (stepModels action.1 model valid))
    obtain ⟨focus,generated,update⟩ := action.1
    cases update with
    | install plan support enabled novel =>
      rcases List.mem_cons.mp recorded with rfl | member
      · exact GeneralNominalInstalledEvidence190.current_instance enabled model valid
      · exact prior member
    | administrative focus next update =>
      apply prior
      cases update <;> exact recorded
    | refresh => exact prior recorded
    | merge => exact prior recorded

/-- Syntactic recorded-node lookup is sound in the actual WF final context. -/
theorem recorded_instance {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) after)
    (model : Assignment) (valid : Models after model)
    (demand : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (recorded : GeneralDictionaryJournalTree.Recorded after.core.erased.current demand key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model demand key children := by
  obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
  exact packet_instance path packet present model valid

/-- Arbitrary finite recorded trees, not only generated fixture trees, have
same-final-model semantics on the actual WF boundary. -/
theorem recorded_tree_sound {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) after)
    (tree : Dictionary roles)
    (syntactic : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryJournalTree.Recorded after.core.erased.current) tree)
    (model : Assignment) (valid : Models after model) :
    (boundary roles).Evidence registry after model tree.root (erase tree) := by
  refine ⟨tree,⟨rfl,rfl⟩,?_⟩
  exact evidence_mono (GeneralDictionaryJournalTree.Recorded after.core.erased.current)
    (GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model)
    (recorded_instance path model valid) syntactic

/-- The tree is chosen independently of the model from finite syntactic coverage
and accessibility. These structural premises are not claimed for all stable states.
No selection preservation, Build or final installability is assumed. -/
theorem uniform_dictionary {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) after)
    (covered : GeneralDictionaryJournalTree.Covered after.core.erased.current root)
    (accessible : Acc (GeneralDictionaryJournalTree.Child after.core.erased.current) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      GeneralSourceDictionaries.Evidence (GeneralDictionaryJournalTree.Recorded after.core.erased.current) tree ∧
      ∀ model, Models after model → (boundary roles).Evidence registry after model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := GeneralDictionaryJournalTree.recorded_tree _ root covered accessible
  exact ⟨tree,same,syntactic,fun model valid => same ▸ recorded_tree_sound path tree syntactic model valid⟩
end Yulang.GeneralNominalOrdinaryJournal194
