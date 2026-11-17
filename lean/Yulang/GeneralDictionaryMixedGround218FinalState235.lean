import Yulang.GeneralDictionaryMixedGround218PointInstall235
import Yulang.GeneralDictionaryMixedGround218RootCommitted235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
/-! Concrete final endpoint of the actual three-step prefix followed by finite
semantic-equality saturation. The choice here constructs a mathematical endpoint;
it is not an executable solver or a general all-step termination theorem. -/
namespace Yulang.GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model)
open GeneralDictionaryMixedGround218PointInstall235 (installed installed_model reachable_installed)
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedEqualityClosure235
open GeneralDictionaryGroundCopy218SaturatedParent (contextFor)

noncomputable def finalState : State roles := Classical.choose (exists_closed installed)

theorem equality_path : Trace installed finalState := (Classical.choose_spec (exists_closed installed)).1

theorem equalities : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed finalState :=
  (Classical.choose_spec (exists_closed installed)).2

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root finalState := by
  obtain ⟨start,initial,path⟩ := reachable_installed
  have append {a b c : State roles}
      (one : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) a b)
      (two : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) b c) :
      B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) a c := by
    induction two with
    | refl => exact one
    | tail _ action ih => exact .tail ih action
  exact ⟨start,initial,append path (trace_steps equality_path registry root)⟩

theorem final_model : Models finalState model := (trace_models equality_path model).mpr installed_model

theorem models_iff (given) : Models finalState given ↔ Models installed given := trace_models equality_path given

noncomputable abbrev allocated := installed.core.erased.current.context.state.allocated
noncomputable abbrev reserved := installed.core.erased.current.context.state.reserved
noncomputable abbrev ordinary := finalState.core.erased.current.context.state.ordinary

theorem installed_context : installed.core.erased.current.context = contextFor allocated reserved
    installed.core.erased.current.context.state.ordinary := rfl

theorem final_context : finalState.core.erased.current.context = contextFor allocated reserved ordinary := by
  rw [trace_shape equality_path]
  change {installed.core.erased.current.context with state :=
    {installed.core.erased.current.context.state with ordinary := ordinary}} = _
  rw [installed_context]

theorem recorded : GeneralDictionaryGroundCopy218Install.plan ∈ finalState.plans := by
  rw [trace_shape equality_path]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

end Yulang.GeneralDictionaryMixedGround218FinalState235
