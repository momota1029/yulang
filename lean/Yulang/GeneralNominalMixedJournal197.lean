import Yulang.GeneralNominalSyntaxRefresh197
import Yulang.GeneralNominalOrdinaryJournal194

set_option backward.isDefEq.respectTransparency false
/-! Journal soundness through a classified subset of actual WF executions.
The classification constrains context updates, not operational semantics. -/
namespace Yulang.GeneralNominalMixedJournal197
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalViewTransport196
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Ordinary growth, or same-slot certified refinement whose old query syntax
is nominal/variable only. Neither arm assumes semantic dictionary transport. -/
def ContextUpdate (registry : Registry) (before after : GeneralNominalCandidates.Context) : Prop :=
  GeneralDictionaryOrdinaryTrace.Extension before after ∨
  ∃ next : View before.state, after = context before next ∧
    ∃ _refinement : GeneralNominalRefinements.Refines before.state (replace before.state next),
    GeneralNominalSyntaxRefresh197.RegistrySyntax registry before

def MixedStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  (boundary roles).Step registry root before after ∧
  ContextUpdate registry before.core.erased.current.context after.core.erased.current.context

theorem steps (path : B4Target.Steps (MixedStep registry root) before after) :
    B4Target.Steps ((boundary roles).Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ action ih => exact .tail ih action.1

theorem instance_update (update : ContextUpdate registry before after)
    (model : Assignment) (valid : GeneralNominalState.Models after.state model)
    (source : GeneralDictionaryRecursiveEvidence.Instance registry before model demand key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after model demand key children := by
  rcases update with ordinary | ⟨next,rfl,refinement,shape⟩
  · exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ ordinary model valid _ _ _ source
  · exact GeneralNominalSyntaxRefresh197.node_transport shape refinement model valid source

theorem universal_evidence (path : B4Target.Steps (MixedStep registry root) before after)
    (source : ∀ model, Models before model →
      (boundary roles).Evidence registry before model demand payload) :
    ∀ model, Models after model → (boundary roles).Evidence registry after model demand payload := by
  induction path with
  | refl => exact source
  | @tail before after path action ih =>
    intro model valid
    obtain ⟨tree,readback,evidence⟩ := ih model (stepModels action.1 model valid)
    refine ⟨tree,readback,?_⟩
    exact evidence_mono _ _ (fun _ _ _ given => instance_update action.2 model valid.1.1.1 given) evidence

/-- Every actually installed packet remains an Instance in each final model,
including across arbitrary interleavings of the two admitted context updates.
No source Instance or final Installable premise is supplied by the caller. -/
theorem packet_instance {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) after)
    (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : packet ∈ after.core.erased.current.packets)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  induction path with
  | refl => cases recorded
  | @tail before after path action ih =>
    have prior (member : packet ∈ before.core.erased.current.packets) :=
      instance_update action.2 model valid.1.1.1 (ih member (stepModels action.1 model valid))
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

theorem recorded_tree_sound {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) after)
    (tree : Dictionary roles)
    (syntactic : Evidence (GeneralDictionaryJournalTree.Recorded after.core.erased.current) tree)
    (model : Assignment) (valid : Models after model) :
    (boundary roles).Evidence registry after model tree.root (erase tree) := by
  refine ⟨tree,⟨rfl,rfl⟩,?_⟩
  apply evidence_mono (GeneralDictionaryJournalTree.Recorded after.core.erased.current)
    (GeneralDictionaryRecursiveEvidence.Instance registry after.core.erased.current.context model) _ syntactic
  intro demand key children recorded
  obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
  exact packet_instance path packet present model valid

/-- Actual journal coverage and accessibility produce a model-independent whole
tree; its semantic validity then holds in every final model of the mixed path. -/
theorem uniform_dictionary {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) after)
    (covered : GeneralDictionaryJournalTree.Covered after.core.erased.current root)
    (accessible : Acc (GeneralDictionaryJournalTree.Child after.core.erased.current) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      Evidence (GeneralDictionaryJournalTree.Recorded after.core.erased.current) tree ∧
      ∀ model, Models after model → (boundary roles).Evidence registry after model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := GeneralDictionaryJournalTree.recorded_tree _ root covered accessible
  exact ⟨tree,same,syntactic,fun model valid => same ▸ recorded_tree_sound path tree syntactic model valid⟩
end Yulang.GeneralNominalMixedJournal197
