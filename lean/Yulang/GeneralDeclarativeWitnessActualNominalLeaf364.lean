import Yulang.GeneralDeclarativeWitnessElectedPayload364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 86000
set_option maxHeartbeats 119000000
namespace Yulang.GeneralDeclarativeWitnessActualNominalLeaf364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessElectedPayload364 (Elected Payload elect recapture key)
open GeneralDeclarativeWitnessActualCompoundElection364 (Read check compound)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessScopedBindings359 (slots)
open GeneralDeclarativeWitnessCompiler350 (Finished execute trip printDemand)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits)
open GeneralDeclarativeWitnessLiteral349 (preserves)
open GeneralDeclarativeWhere319 (Capture)

def layout {contra x t} {w : @Elected contra x t key} (p : Payload w) : Layout :=
  ⟨t.sourceRoot.world.ordinary,[(w.unary.binder,p.capture)],[60,61,62,301,302,303],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Leaf {contra : Bool} {x : Ordered contra} (t : Read x) where
  elected : Elected t key
  payload : Payload elected
  body : Prepared t.environment key t.sourceRoot.occurrence (layout payload)
  source : body.impl = elected.row
  actual : Capture
  read : slots [body.captures] key elected.unary.binder = some actual
  center : actual.center = payload.capture.center
  executed : Finished
  runs : execute (context t.environment t.sourceRoot.occurrence body.impl (layout payload)) = some executed
  retained : preserves t.sourceRoot.world.ordinary executed.state = true
  noWrites : executed.fixed = []
  noKids : executed.kids = []

def compile {contra} {x : Ordered contra} (t : Read x) : Option (Leaf t) := do
  let w ← elect t key
  let p ← recapture w
  let result ← prepare t.environment key t.sourceRoot.occurrence (layout p)
  match slot : slots [result.captures] key w.unary.binder with
  | none => none
  | some a =>
    if center : a.center = p.capture.center then
      match ran : execute (context t.environment t.sourceRoot.occurrence result.impl (layout p)) with
      | none => none
      | some e =>
        if verified : preserves t.sourceRoot.world.ordinary e.state = true ∧ e.fixed = [] ∧ e.kids = [] then
          some ⟨w,p,result,Option.some.inj (result.authored.symm.trans w.sourceOrdinal),
            a,slot,center,e,ran,verified.1,verified.2.1,verified.2.2⟩
        else none
    else none

def Leaf.world {contra x t} (s : @Leaf contra x t) : World :=
  ⟨s.executed.state,t.sourceRoot.world.board⟩

structure FinishedRun {contra : Bool} (x : Ordered contra) where
  inspected : Read x
  leaf : Leaf inspected

def demo {contra} (x : Ordered contra) : Option (FinishedRun x) := do
  let t ← check x [compound (GeneralDeclarativeWitnessThreeNative362.ctor contra)]
  let s ← compile t
  pure ⟨t,s⟩

def actual {contra x} (f : @FinishedRun contra x) : Bool :=
  decide (f.inspected.sourceRoot.chosen.impl.id = 97 ∧ f.leaf.elected.row.id = 99 ∧
    printDemand f.inspected.sourceRoot.occurrence = (11,[(310,302,311)],[]) ∧
    trip f.leaf.payload.capture = (60,61,62) ∧ f.leaf.actual.center = 61)

theorem actual_elected_compound_has_literal_receipt (contra : Bool) :
    ((run contra).bind fun x => (demo x).map actual).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessActualNominalLeaf364
