import Yulang.GeneralDeclarativeWitnessActualCompoundElection364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 85000
set_option maxHeartbeats 115000000
namespace Yulang.GeneralDeclarativeWitnessElectedPayload364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (Projection Spine spine)
open GeneralDeclarativeWitnessActualCompoundElection364 (Read check compound)
open GeneralDeclarativeWitnessCompoundCandidate364 (Unary convert)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessCompiler350 (trip)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativeRelease360 (checked_exact_written_value)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration)

structure Elected {contra : Bool} {x : Ordered contra} (t : Read x) (atFrame : FrameKey) where
  row : Declaration
  alone : t.inspected.hits = [row]
  sourceOrdinal : t.environment.source.declarations[atFrame.sourceOrdinal]? = some row
  sourceId : row.id = atFrame.declaration
  unary : Unary t.environment t.sourceRoot.occurrence row
  positive : unary.ctor = t.independently.a.head

def elect {contra} {x : Ordered contra} (t : Read x) (f : FrameKey) : Option (Elected t f) := do
  match got : t.inspected.hits with
  | [row] =>
    let unary ← convert t.environment t.sourceRoot.occurrence row
    if exposed : t.environment.source.declarations[f.sourceOrdinal]? = some row ∧
        row.id = f.declaration ∧ unary.ctor = t.independently.a.head then
      some ⟨row,got,exposed.1,exposed.2.1,unary,exposed.2.2⟩
    else none
  | _ => none

def key : FrameKey := ⟨[10,0],99,1⟩

def makeCapture (variance : Bool) (a center b : Nat) : Capture :=
  if variance then ⟨b,center,a⟩ else ⟨a,center,b⟩

structure Payload {contra : Bool} {x : Ordered contra} {t : Read x} {f : FrameKey} (won : Elected t f) where
  center : Spine x.center.native.write.code
  same : center.head = won.unary.ctor
  target : x.center.native.write.address.target = t.sourceRoot.span.center
  distinct : t.independently.a.payload ≠ t.independently.b.payload

def recapture {contra} {x : Ordered contra} {t : Read x} {f : FrameKey} (won : Elected t f) :
    Option (Payload won) := do
  let c ← spine x.center.native.write.code
  if ok : c.head = won.unary.ctor ∧ x.center.native.write.address.target = t.sourceRoot.span.center ∧
      t.independently.a.payload ≠ t.independently.b.payload then
    pure ⟨c,ok.1,ok.2.1,ok.2.2⟩
  else none

def Payload.capture {contra x t f won} (p : @Payload contra x t f won) : Capture :=
  makeCapture won.unary.variance t.independently.a.payload p.center.payload t.independently.b.payload

theorem independent_center_read_after_election {contra} {x : Ordered contra} {t : Read x}
    {f : FrameKey} {won : Elected t f} (p : Payload won) (m : Assignment) (v : NativeViews)
    (fit : Fits t.sourceRoot.world m v) :
    v t.sourceRoot.span.center = some (.unary won.unary.ctor (.leaf (m p.capture.center).1)) := by
  have origin : Fits x.after.final m v :=
    ⟨(GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared t.sourceRoot.body m fit.1).1,fit.2⟩
  have read := checked_exact_written_value (w := x.after.final) t.sourceRoot.ready.nativeInput.openedMid m v origin
  rw [p.target,p.center.exact,p.same] at read
  have center : p.capture.center = p.center.payload := by
    unfold Payload.capture makeCapture
    split <;> rfl
  simpa only [center,Code.eval] using read

def exact {contra} (x : Ordered contra) : Bool :=
  ((check x [compound (GeneralDeclarativeWitnessThreeNative362.ctor contra)]).bind fun t =>
    (elect t key).bind fun won => (recapture won).map fun p =>
      decide (won.unary.binder = 93 ∧ won.unary.variance = contra ∧ trip p.capture = (60,61,62))).getD false

theorem actual_elected_payload_is_oriented_without_guessing_center (contra : Bool) :
    ((run contra).map exact).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessElectedPayload364
