import Yulang.GeneralDictionarySettledPendingExclusion
import Yulang.GeneralNominalSettledPump

/-! Concrete-model cut certificates now rule out dictionary selection at the
new boundary, including completion of selected ancestors. The cut witness and
inspection point remain explicit; this does not assert a realized pump prefix. -/
namespace Yulang.GeneralDictionarySettledCutExclusion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSettledBoundary
open GeneralNominalSettledPump GeneralNominalSettledSupport
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}
variable {root : Occurrence roles} {producer : Packet roles}
variable {model : GeneralNominalCommonBridge.Assignment}

theorem inspected_cut_no_dictionary (point : InspectionPoint registry state root)
    (cut : OutputCut state producer model) (unfinished : Unsettled state.current producer)
    (scalar : (model (state.current.context.state.base.source point.slot)).1 = .base .int)
    (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (boundary roles).toSourceBoundary registry state root (.selected dictionary) :=
  GeneralDictionarySettledPendingExclusion.no_selected_classification registry state root
    (inspected_cut_pending point cut unfinished scalar) dictionary

theorem inspected_cut_no_completed (point : InspectionPoint registry state root)
    (cut : OutputCut state producer model) (unfinished : Unsettled state.current producer)
    (scalar : (model (state.current.context.state.base.source point.slot)).1 = .base .int)
    (tree : Tree) (dictionary : Dictionary)
    (resolved : Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) root tree) :
    ¬ B4TargetV3.Completed tree (.selected dictionary) :=
  GeneralDictionarySettledPendingExclusion.no_completed_selected registry state root
    (inspected_cut_pending point cut unfinished scalar) tree dictionary resolved

theorem descendant_cut_no_completed (child : Occurrence roles)
    (path : B4Target.Steps
      (fun parent child => Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) child parent)
      root child)
    (point : InspectionPoint registry state child)
    (cut : OutputCut state producer model) (unfinished : Unsettled state.current producer)
    (scalar : (model (state.current.context.state.base.source point.slot)).1 = .base .int)
    (tree : Tree) (dictionary : Dictionary)
    (resolved : Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary registry state) root tree) :
    ¬ B4TargetV3.Completed tree (.selected dictionary) :=
  GeneralDictionarySettledPendingExclusion.descendant_pending_no_completed registry state root child path
    (inspected_cut_pending point cut unfinished scalar) tree dictionary resolved
end Yulang.GeneralDictionarySettledCutExclusion
