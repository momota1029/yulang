import Yulang.GeneralNominalStructuralReadback
import Yulang.GeneralNominalSourceFrontier

/-! Direct point and structural paths in the finite frontier denote their
actual terminal identities. A terminal recursive component remains opaque. -/
namespace Yulang.GeneralNominalFrontierReadback
open GeneralNominalRecursiveInspection GeneralNominalSourceFrontier
open GeneralNominalActualInspectionSteps GeneralNominalOriginTerms
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls}

theorem child_readback (state : GeneralNominalSaturationState.State roles)
    {label : Label} {first last : Fin state.context.state.base.slots}
    (edge : (label,last) ∈ children state.context.state first) :
    Represents state (label.apply (.source (state.context.state.base.source first)))
      (state.context.state.base.source last) := by
  rcases List.mem_append.mp edge with structural | nominal
  · unfold structuralChildren at structural
    split at structural
    · rename_i kind values recorded
      obtain ⟨index,equal⟩ := List.mem_ofFn.mp structural
      cases equal
      exact GeneralNominalStructuralReadback.actual_structural_readback state first kind values recorded index
    · cases structural
  · unfold nominalChildren at nominal
    split at nominal
    · cases nominal
    · rename_i descriptor recorded
      obtain ⟨value,present,equal⟩ := List.mem_filterMap.mp nominal
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
      dsimp only [id] at equal
      split at equal
      · rename_i lower upper found
        split at equal
        · rename_i same
          cases equal
          apply point_argument_readback state first _ descriptor recorded
          rw [List.getElem?_eq_getElem index.isLt]
          exact congrArg some (found.trans (by rw [same]))
        · cases equal
      · cases equal

private theorem label_observation {model : GeneralNominalCommonBridge.Assignment} (same : Same model first last) (label : Label)
    (seen : Observes model (label.apply first) value) : Observes model (label.apply last) value := by
  obtain ⟨other,observed⟩ := same.2.1
  cases label with
  | structural shape index =>
    cases seen with
    | structural parent length equal found =>
      have comparison := same.2.2 _ _ parent observed
      exact .structural observed length
        ⟨subtype_trans comparison.2 equal.1,subtype_trans equal.2 comparison.1⟩ found
  | nominal name index =>
    cases seen with
    | nominal parent equal found =>
      have comparison := same.2.2 _ _ parent observed
      exact .nominal observed
        ⟨subtype_trans comparison.2 equal.1,subtype_trans equal.2 comparison.1⟩ found

theorem label_readback {state : GeneralNominalSaturationState.State roles} {label : Label} (represented : Represents state root identity)
    (readback : Represents state (label.apply (.source identity)) terminal) :
    Represents state (label.apply root) terminal := by
  intro model valid
  have same := represented model valid
  obtain ⟨⟨value,seen⟩,other,all⟩ := readback model valid
  refine ⟨⟨value,label_observation (same_symm same) label seen⟩,other,?_⟩
  intro a b one two
  exact all a b (label_observation same label one) two

theorem walk_readback (state : GeneralNominalSaturationState.State roles)
    {first last : Fin state.context.state.base.slots}
    {inspected : List (Fin state.context.state.base.slots)}
    (walk : Walk state.context.state first root inspected last result)
    (represented : Represents state root (state.context.state.base.source first)) :
    Represents state result (state.context.state.base.source last) := by
  induction walk with
  | stop => exact represented
  | next edge safe walk ih => exact ih (label_readback represented (child_readback state edge))

theorem source_walk (state : GeneralNominalSaturationState.State roles)
    {first last : Fin state.context.state.base.slots}
    {inspected : List (Fin state.context.state.base.slots)}
    (walk : Walk state.context.state first (.source (state.context.state.base.source first)) inspected last result) :
    result ∈ frontier state.context.state ∧
      Represents state result (state.context.state.base.source last) :=
  ⟨frontier_covers walk,walk_readback state walk (fun model _ => source_self model _)⟩

theorem step_preserves (step : Step registry focus before after)
    (represented : Represents before.current origin identity) :
    Represents after.current origin identity :=
  fun model valid => represented model (GeneralNominalSharedSteps.step_models (step_shared step) model valid)

theorem trace_preserves (path : B4Target.Steps (Step registry focus) before after)
    (represented : Represents before.current origin identity) :
    Represents after.current origin identity := by
  induction path with
  | refl => exact represented
  | tail path step ih => exact step_preserves step ih

theorem source_walk_survives (before : GeneralNominalSupport.Tracked roles)
    {first last : Fin before.current.context.state.base.slots}
    {inspected : List (Fin before.current.context.state.base.slots)}
    (walk : Walk before.current.context.state first
      (.source (before.current.context.state.base.source first)) inspected last result)
    (path : B4Target.Steps (Step registry focus) before after) :
    result ∈ frontier before.current.context.state ∧
      Represents after.current result (before.current.context.state.base.source last) :=
  ⟨frontier_covers walk,trace_preserves path (source_walk before.current walk).2⟩

end Yulang.GeneralNominalFrontierReadback
