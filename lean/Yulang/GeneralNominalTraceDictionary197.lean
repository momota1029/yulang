import Yulang.GeneralNominalInspectionTrace197
import Yulang.GeneralNominalViewRefresh196

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalTraceDictionary197
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalViewTransport196
open GeneralNominalInspectionTrace197

/-- At one used key, successful observation traces are needed only for its
actual source argument lookup. Deferred queries have no successful trace. -/
def AtNode (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments old root = some bounds →
      Traces old.state next
        (GeneralNominalInspection.queries old.state old.interpretation declaration) bounds

inductive TreeTrace (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state) : Dictionary roles → Prop where
  | node (atNode : AtNode registry old next root key)
      (children : ∀ child ∈ trees, TreeTrace registry old next child) :
      TreeTrace registry old next (.node root key trees)

theorem support (traced : TreeTrace registry old next tree) :
    GeneralNominalRootedView196.Support registry old next tree := by
  induction traced with
  | node atNode _ ih =>
    exact .node (fun declaration member identity bounds located =>
      rechecked_of_trace old next declaration bounds (atNode declaration member identity bounds located)) ih

theorem tree_transport (traced : TreeTrace registry old next tree)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model) tree :=
  GeneralNominalRootedView196.tree_transport (support traced) model valid source

/-- The identical complete payload and assignment are retained; this is not a
fresh producer of source evidence or a proof of the general EvidenceNode. -/
theorem readback_transport (traced : TreeTrace registry old next tree)
    (readback : Readback root payload tree) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (context old next) model root payload :=
  GeneralNominalRootedView196.readback_transport (support traced) readback model valid source

/-- For an actual WF refresh certificate, all final assignments restrict to
initial assignments. A single finite traced witness suffices uniformly. -/
theorem universal_refresh {state : GeneralNominalCenteredHeadStepEffects.State roles}
    {next : View state.core.erased.current.context.state}
    (certificate : GeneralNominalCenteredSteps.Refresh state.core
      (context state.core.erased.current.context next))
    (traced : TreeTrace registry state.core.erased.current.context next tree)
    (readback : Readback root payload tree)
    (source : ∀ model, GeneralNominalCenteredHeadStepEffects.Models state model →
      GeneralSourceDictionaries.Evidence
        (GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model) tree) :
    ∀ model, GeneralNominalCenteredHeadStepEffects.Models
      (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next)) model →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry
        (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next))
        model root payload := by
  intro model valid
  apply readback_transport traced readback model valid.1.1.1
  exact source model ((GeneralNominalCenteredHeadStepKernel.refresh_models certificate model).mp valid)
end Yulang.GeneralNominalTraceDictionary197
