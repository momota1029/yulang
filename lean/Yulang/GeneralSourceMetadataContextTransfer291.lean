import Yulang.GeneralSourceMetadataInspectTransport291
import Yulang.GeneralSourceMetadataReportMeaning291

/-! The translated query and the report transport are separately checked.
Only local head agreement is needed for this observation, not old full
Metadata, old Frame, or another reachable raw journal. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataContextTransfer291
open GeneralDeclarations (Declaration)
open GeneralNominalCandidates (Context)
open GeneralNominalState (State)
open GeneralNominalInspection (Bounds queries)
open GeneralNominalRecursiveInspection (Report ProjectionModels inspectMany bindings selfChecks Finished)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataRows291 (Source constructors interpretation)
open GeneralSourceMetadataSnapshot291 (Fits context retag)
open GeneralSourceMetadataReport291 (lower)
open GeneralSourceMetadataInspectTransport291 (many_lower)
open GeneralSourceMetadataReportMeaning291 (lower_projection lower_bindings lower_self_checks lower_finished)
open GeneralObservedMetadataKeys290 (headKeys)
open GeneralObservedMetadataEntry290 (LocalEqual agree agree_exact)

theorem lower_checked (s : State) (src : Source) (fit : Fits s src)
    (res : Report (retag s src fit)) (bs : List (Bounds s)) :
    lower s src fit { res with checked := (show List (Bounds (retag s src fit)) from bs) ++ res.checked } =
      { lower s src fit res with checked := bs ++ (show List (Bounds s) from res.checked) } := rfl

theorem report_transport (old : Context) (src : Source) (fit : Fits old.state src)
    (d : Declaration) (bounds : List (Bounds old.state))
    (agreeLocal : LocalEqual (headKeys d) old.state.constructors old.interpretation
      (constructors src) (interpretation src)) :
    lower old.state src fit (report (context old.state src fit) d bounds) = report old d bounds := by
  have queries' : queries (context old.state src fit).state
      (context old.state src fit).interpretation d = queries old.state old.interpretation d :=
    (GeneralObservedMetadataReport290.queries_eq _ _ _ _ d agreeLocal).symm
  unfold report
  rw [queries',lower_checked]
  have same := many_lower old.state src fit (queries old.state old.interpretation d) bounds (fun _ => none) 0
  exact congrArg (fun (value : Report old.state) => { value with checked := bounds ++ value.checked }) same

theorem checked_report_transport (old : Context) (src : Source) (fit : Fits old.state src)
    (d : Declaration) (bounds : List (Bounds old.state))
    (certificate : agree (headKeys d) old.state.constructors old.interpretation
      (constructors src) (interpretation src) = true) :
    lower old.state src fit (report (context old.state src fit) d bounds) = report old d bounds :=
  report_transport old src fit d bounds ((agree_exact ..).mp certificate)

theorem meaning_transport (old : Context) (src : Source) (fit : Fits old.state src)
    (d : Declaration) (bounds : List (Bounds old.state))
    (agreeLocal : LocalEqual (headKeys d) old.state.constructors old.interpretation
      (constructors src) (interpretation src)) (m : Assignment) :
    let new := context old.state src fit
    let incoming := report new d bounds
    let prior := report old d bounds
    bindings new.state incoming = bindings old.state prior ∧
    selfChecks new.state incoming = selfChecks old.state prior ∧
    (Finished incoming ↔ Finished prior) ∧
    (ProjectionModels new.state incoming m ↔ ProjectionModels old.state prior m) := by
  have preserved := report_transport old src fit d bounds agreeLocal
  dsimp only
  rw [← preserved]
  exact ⟨(lower_bindings _ _ _ _).symm,(lower_self_checks _ _ _ _).symm,
    (lower_finished _ _ _ _).symm,(lower_projection _ _ _ _ m).symm⟩

end Yulang.GeneralSourceMetadataContextTransfer291
