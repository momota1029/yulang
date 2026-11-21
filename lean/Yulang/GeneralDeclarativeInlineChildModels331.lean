import Yulang.GeneralDeclarativeInlineChildResult331
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeInlineChildModels331
open GeneralDeclarativeInlineDecl331 hiding child
open GeneralDeclarativeInlineChildFrame331
open GeneralDeclarativeInlineChildResult331 (dict tree all_models)
open GeneralDeclarativeInlineChildGuards331 (output_not_promoted)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEntailment320 (model_append appendFacts)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeRecordPoints330 (named precise)
open GeneralDeclarativeRecordSpine330 (exact_subtraction)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty record exactEmpty)
open CommonNominalFullCarrier (pair)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeStableCompiler329 (read)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)

abbrev flag : Ty := .base .bool
abbrev payload := pair flag int
abbrev residualTy := record 9 flag exactEmpty
abbrev rootTy := record 7 payload (record 7 int (record 8 int residualTy))

def model : Assignment := fun n =>
  (if n = 0 then rootTy else if n = 18 ∨ n = 5 then payload else
    if n = 6 ∨ n = 19 then residualTy else if n = 4 ∨ n = 15 then flag else int,Common.rowEmpty)

theorem initial_valid : Models sourceState model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro row used
  change row ∈ [rawRow,scalar] at used
  rcases List.mem_cons.mp used with rfl|other
  · exact eqv_refl _
  · cases List.mem_singleton.mp other
    exact eqv_refl _

theorem actual_names :
    Models (GeneralDeclarativeRecordPoints330.named sourceState 0 keep chosen remainder) model := by
  apply (model_append _).mpr
  refine ⟨initial_valid,fun row used => ?_⟩
  change row ∈ [⟨18,compound⟩,⟨19,remainder⟩] at used
  rcases List.mem_cons.mp used with rfl|rest
  · exact eqv_refl _
  · cases List.mem_singleton.mp rest
    exact eqv_refl _

theorem head_row : Models rebuilt model := by
  apply (model_append _).mpr
  refine ⟨actual_names,fun row used => ?_⟩
  cases List.mem_singleton.mp used
  have visible := exact_subtraction (raw_closed (fun _ => False)) (keys := [7,8]) (by decide)
    (show GeneralDeclarativeOrderedRecord326.order (CommonRoleCanonicalRows.normalize raw) [7,8]
      = some chosen from rfl) model initial_valid
  have known := (model_append _).mp actual_names
  have each := precise chosen remainder 18 model known.2
  exact eqv_trans visible (eqv_symm each)

theorem final_valid : Models final model := by
  apply (model_append _).mpr
  refine ⟨(model_append _).mpr ⟨head_row,?_⟩,?_⟩
  all_goals
    intro e h
    cases List.mem_singleton.mp h
    exact eqv_refl _

theorem exact_compiler :
    Result final (facts registry interpretation frame.capture decl root [child]) :=
  (read checked covered List.mem_cons_self rfl declared frame).1

/-- Actual source inline field 7 gets a fresh compound capture; its fresh
logical name is proven to come from an independently supported RHS
and is consumed by the actual generated child. The fixed root target
receives the exact remainder with the buried label removed. The
current source guards and compiler have a nonvacuous common model. -/
theorem checked_dictionary :
    frame.capture 0 = point 18 ∧ frame.capture 3 = point 3 ∧ frame.capture 1 = point 19 ∧
      frame.rootRows = [⟨6,.variable 19⟩] ∧ Models final model ∧
      Evidence registry interpretation model root dict :=
  ⟨rfl,rfl,rfl,rfl,final_valid,all_models model final_valid⟩

end Yulang.GeneralDeclarativeInlineChildModels331
