import Yulang.GeneralNominalSlotTransport198
import Yulang.GeneralNominalMixedJournal197
import Yulang.GeneralNominalJournalAccessibility194
import Yulang.GeneralNominalOrdinaryJournal194

set_option backward.isDefEq.respectTransparency false
/-! Journal soundness through a classified subset of actual WF executions.
The classification constrains context updates, not operational semantics. -/
namespace Yulang.GeneralNominalRefiningJournal198
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalViewTransport196
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Ordinary growth, or arbitrary-slot certified refinement whose old query syntax
is nominal/variable only. Neither arm assumes semantic dictionary transport. -/
def ContextUpdate (registry : Registry) (before after : GeneralNominalCandidates.Context) : Prop :=
  GeneralDictionaryOrdinaryTrace.Extension before after ∨
  ∃ _refinement : GeneralNominalRefinements.Refines before.state after.state,
    after.interpretation = before.interpretation ∧
    GeneralNominalSyntaxRefresh197.RegistrySyntax registry before

def MixedStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  (boundary roles).Step registry root before after ∧
  ContextUpdate registry before.core.erased.current.context after.core.erased.current.context

/-- The old same-slot class is included, but no longer required. -/
theorem old_step (step : GeneralNominalMixedJournal197.MixedStep registry root before after) :
    MixedStep registry root before after := by
  refine ⟨step.1,?_⟩
  rcases step.2 with ordinary | ⟨next,equal,refinement,shape⟩
  · exact Or.inl ordinary
  · exact Or.inr ⟨equal ▸ refinement,equal ▸ rfl,shape⟩

theorem refresh_step {state : State roles} {context : GeneralNominalCandidates.Context}
    (certificate : GeneralNominalCenteredSteps.Refresh state.core context)
    (shape : GeneralNominalSyntaxRefresh197.RegistrySyntax registry state.core.erased.current.context)
    (source : Nat) (present : source ∈ GeneralNominalState.sources state.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.core.erased.current.context.state source)
    (known : GeneralNominalState.Known context.state source) :
    MixedStep registry root state (refresh state context) :=
  ⟨⟨root,.root,.refresh root context certificate source present unknown known⟩,
    Or.inr ⟨certificate.refines,certificate.interpretation,shape⟩⟩

theorem steps (path : B4Target.Steps (MixedStep registry root) before after) :
    B4Target.Steps ((boundary roles).Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ action ih => exact .tail ih action.1

theorem instance_update (update : ContextUpdate registry before after)
    (model : Assignment) (valid : GeneralNominalState.Models after.state model)
    (source : GeneralDictionaryRecursiveEvidence.Instance registry before model demand key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after model demand key children := by
  rcases update with ordinary | ⟨refinement,interpretation,shape⟩
  · exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ ordinary model valid _ _ _ source
  · exact GeneralNominalSlotTransport198.node_transport shape refinement interpretation model valid source

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

/-- Actual journal coverage and the finite state-derived rank produce a model-independent whole
tree; its semantic validity then holds in every final model of the mixed path. -/
theorem uniform_dictionary {context : GeneralNominalCandidates.Context} {after : State roles}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) after)
    (covered : GeneralDictionaryJournalTree.Covered after.core.erased.current root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      Evidence (GeneralDictionaryJournalTree.Recorded after.core.erased.current) tree ∧
      ∀ model, Models after model → (boundary roles).Evidence registry after model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := GeneralNominalJournalAccessibility194.recorded_tree _ root covered
  exact ⟨tree,same,syntactic,fun model valid => same ▸ recorded_tree_sound path tree syntactic model valid⟩
end Yulang.GeneralNominalRefiningJournal198
