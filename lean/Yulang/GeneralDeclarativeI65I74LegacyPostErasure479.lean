import Yulang.GeneralDeclarativeI65I74BeforeCaptureRun475
import Yulang.GeneralDeclarativeI65I74ReadOldCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open C466WrittenBinderCoordinates (OldCaptureReceipt readOldCaptureReceipt)

def emitFromOldSourceView479 (p : FullProblem) (w : BeforeCaptureWire)
    (arg : Capture) (pattern : Pattern) (job : Nat) : Option OldCaptureReceipt :=
  readOldCaptureReceipt (rawAt p) (oldInputIndex p w) (authoredRegistry p.old.state.core.current).constructors
    (interpretation p.old.state.core.current.environment.source.snapshot) arg [] pattern job

theorem exact_old_source_view_agreement_controls_every_legacy_emission479
    (p : FullProblem) (l r : BeforeCaptureWire)
    (old : offeredInputView p l = offeredInputView p r)
    (arg : Capture) (pattern : Pattern) (job : Nat) :
    emitFromOldSourceView479 p l arg pattern job = emitFromOldSourceView479 p r arg pattern job := by
  let project := fun (s : GeneralDeclarativeHead320.State) =>
    readOldCaptureReceipt (rawAt p)
       (GeneralDeclarativeNestedIndex332.ofRows (s := s) s.equations (fun _ h => h))
       (authoredRegistry p.old.state.core.current).constructors
       (interpretation p.old.state.core.current.environment.source.snapshot) arg [] pattern job
  exact congrArg project old


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
