import Yulang.GeneralNominalMixedJournal197
import Yulang.GeneralNominalSyntaxExample197

set_option backward.isDefEq.respectTransparency false
/-! A real enqueue followed by a descriptor-changing refresh. The initial
fixture is explicitly unqueued; no Initial/Reachable assertion is made. -/
namespace Yulang.GeneralNominalMixedExample197
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMixedJournal197
open GeneralNominalTraceRefreshExample197 (registry focus payload)
open GeneralNominalExecutableView196 (start finish next certificate)
open GeneralNominalRefreshFork (root context)
open GeneralDeclarationExamples (roles)

def unqueued : State roles :=
  {start with core := {start.core with erased := {start.core.erased with
    current := {start.core.erased.current with sites := []}}}}

theorem enqueue_step : (boundary roles).Step registry root unqueued start := by
  refine ⟨root,.root,?_⟩
  exact .administrative root (GeneralNominalSaturationState.enqueue unqueued.core.erased.current root)
    (.enqueue root (GeneralNominalRefreshFork.linked none) (by intro site member; cases member))

theorem ordinary_step : MixedStep registry root unqueued start :=
  ⟨enqueue_step,Or.inl (GeneralDictionaryOrdinaryTrace.extension_refl _)⟩

theorem refresh_step (wide : Bool) : MixedStep registry root start (finish wide) :=
  ⟨GeneralNominalExecutableView196.actual_step registry wide,
    Or.inr ⟨next wide,rfl,(certificate wide).refines,GeneralNominalSyntaxExample197.registry_syntax⟩⟩

theorem mixed_path (wide : Bool) :
    B4Target.Steps (MixedStep registry root) unqueued (finish wide) :=
  .tail (.tail .refl ordinary_step) (refresh_step wide)

theorem actual_path (wide : Bool) :
    B4Target.Steps ((boundary roles).Step registry root) unqueued (finish wide) :=
  steps (mixed_path wide)

theorem source_payload (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models unqueued model) :
    (boundary roles).Evidence registry unqueued model focus payload :=
  ⟨GeneralNominalTraceRefreshExample197.tree,GeneralNominalTraceEvidence197.source_readback,
    GeneralNominalTraceEvidence197.source_tree model valid.1.1.1⟩

theorem final_payload (wide : Bool) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models (finish wide) model) :
    (boundary roles).Evidence registry (finish wide) model focus payload :=
  universal_evidence (mixed_path wide) source_payload model valid

theorem real_changes (wide : Bool) :
    unqueued.core.erased.current.sites ≠ start.core.erased.current.sites ∧
    start.core.erased.current.context.state.nominals ⟨0,by change 0 < 5; decide⟩ ≠
      (finish wide).core.erased.current.context.state.nominals ⟨0,by change 0 < 5; decide⟩ := by
  constructor
  · intro equal; cases equal
  · cases wide <;> intro equal <;> cases equal

theorem inhabited (wide : Bool) : Models unqueued GeneralNominalRefreshFork.model ∧
    Models (finish wide) GeneralNominalRefreshFork.model ∧
    (boundary roles).Evidence registry (finish wide) GeneralNominalRefreshFork.model focus payload := by
  have final := (GeneralNominalExecutableView196.inhabited wide).2
  exact ⟨steps_models (actual_path wide) _ final,final,final_payload wide _ final⟩
end Yulang.GeneralNominalMixedExample197
