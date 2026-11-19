import Yulang.GeneralRebaseCompoundChildEntry273

namespace Yulang.GeneralRebaseCompoundOwnerRegression273
open GeneralRebaseCompoundOwnerBlock273 (compile loBind pointBind)
open GeneralRebaseCompoundOwnerStep273 (Stage next PublicMeaning)
open GeneralRebaseCompoundPublic273 (AgreesTypes)
open GeneralNominalCommonBridge (Assignment)

theorem reject_empty : compile [] 2 = none := rfl

theorem reject_nondoubled : compile [(0,4,2)] 2 = none := rfl

theorem reject_diverging_endpoint : compile [(0,4,2),(0,2,2)] 2 = none := rfl

theorem reject_nonpublic_endpoint : compile [(0,5,2),(0,5,2)] 2 = none := rfl

theorem reject_wrong_owner_name : compile [(1,4,2),(1,4,2)] 2 = none := rfl

theorem reject_center_guess : next .initial loBind 4 = none := rfl

theorem reject_point_without_install : next .initial pointBind 2 = none := rfl

def drive : Stage → List (GeneralNominalAllocation.Bindings × Fin 5) → Option Stage
 | stage,[] => some stage
 | stage,(input,center)::rest => (next stage input center).bind (fun found => drive found rest)

theorem exact_script :
 drive .initial [(loBind,2),(pointBind,2)] = some .replacement := rfl

theorem reject_reversed :
 drive .initial [(pointBind,2),(loBind,2)] = none := rfl

theorem reject_third :
 drive .initial [(loBind,2),(pointBind,2),(pointBind,2)] = none := rfl

theorem meaning_reads_only_public_types (stage : Stage) (first last : Assignment)
 (same : AgreesTypes first last) : PublicMeaning stage first ↔ PublicMeaning stage last := by
 unfold PublicMeaning
 refine and_congr (GeneralRebaseCompoundSourceTypes273.source_depends_on_types first last same) ?_
 unfold GeneralRebaseCompoundSourceTypes273.Body
 rw [same 4 (by decide)]

end Yulang.GeneralRebaseCompoundOwnerRegression273
