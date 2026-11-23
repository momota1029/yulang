import Yulang.GeneralDeclarativeWitnessSelectedNonpointRoot363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 77000
set_option maxHeartbeats 95000000
namespace Yulang.GeneralDeclarativeWitnessSelectedNonpointChild363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root emit)
open GeneralDeclarativeWitnessNonpointGraph363 (Safe graph graph_exact_positive)
open GeneralDeclarativeWitnessLocatedElection363 (Chosen choose exact_compiler_must_use_chosen_row)
open GeneralDeclarativeWitnessNonpointPort362 (env)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand trip)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)

def path : FrameKey := ⟨[10,0],98,1⟩

structure Issued {contra : Bool} {x : Ordered contra} {e : Environment} (r : Root x e) : Type where
  copied : r.occurrence.arguments = [r.span]
  separated : r.span.lower ≠ r.span.center ∧ r.span.center ≠ r.span.upper
  recurrence : Safe r.world

/-- A child is an actual source occurrence with its own served graph
and an upstream exact native-origin proof. Mere numerical equality at
a rebound alias is not treated as a new native release. -/
def backedOccurrence {contra} {x : Ordered contra} {e : Environment} (r : Root x e) : Option (Issued r) :=
  if positions : r.span.lower ≠ r.span.center ∧ r.span.center ≠ r.span.upper then
    if acyclic : graph r.world then
      some ⟨r.input,positions,graph_exact_positive acyclic⟩
    else none
  else none

def layout {contra x e} (root : @Root contra x e) (ch : Chosen e root.occurrence path) : Layout :=
  ⟨root.world.ordinary,ch.fitBare.captures,[60,61,62,201,202,203],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Child {contra : Bool} {x : Ordered contra} {e : Environment} (r : Root x e) where
  issued : Issued r
  chosen : Chosen e r.occurrence path
  prepared : Prepared e path r.occurrence (layout r chosen)
  actual : prepared.impl = chosen.impl
  binder : Capture
  read : slots [prepared.captures] path 92 = some binder
  center : binder.center = r.span.center
  body : Finished
  ran : execute (context e r.occurrence prepared.impl (layout r chosen)) = some body
  stays : preserves r.world.ordinary body.state = true
  emptyOutput : body.fixed = []
  doneChildren : body.kids = []

def enter {contra} {x : Ordered contra} {e : Environment} (r : Root x e) : Option (Child r) := do
  let ready ← backedOccurrence r
  let winner ← choose e r.occurrence path
  let frame ← prepare e path r.occurrence (layout r winner)
  match had : slots [frame.captures] path 92 with
  | none => none
  | some binder =>
    if saved : binder.center = r.span.center then
      match ran : execute (context e r.occurrence frame.impl (layout r winner)) with
      | none => none
      | some result =>
        if exact : preserves r.world.ordinary result.state = true ∧ result.fixed = [] ∧ result.kids = [] then
          some ⟨ready,winner,frame,exact_compiler_must_use_chosen_row winner frame,binder,had,saved,result,ran,
            exact.1,exact.2.1,exact.2.2⟩
        else none
    else none

def Child.world {contra x e r} (c : @Child contra x e r) : World := ⟨c.body.state,r.world.board⟩

structure Complete {contra : Bool} (x : Ordered contra) where
  environment : Environment
  parent : Root x environment
  child : Child parent

def close {contra} (x : Ordered contra) : Option (Complete x) := do
  let e ← env
  let root ← emit x e
  let child ← enter root
  pure ⟨e,root,child⟩

def actual {contra x} (s : @Complete contra x) : Bool :=
  decide (s.parent.chosen.impl.id = 97 ∧ s.child.chosen.impl.id = 98 ∧
    printDemand s.parent.occurrence = (11,[(310,302,311)],[]) ∧ trip s.child.binder = (314,302,315))

theorem actual_selected_replay (contra : Bool) :
    ((run contra).bind fun x => (close x).map actual).getD false = true := by
  cases contra <;> decide +kernel

theorem returned_model_has_prior_author_and_child_state {contra} {x : Ordered contra} {e : Environment}
    {r : Root x e} (child : Child r) (m : Assignment) (v : NativeViews) (f : Fits child.world m v) :
    Fits r.world m v ∧ Fits x.after.final m v := by
  have before := restrict ((preserves_iff ..).mp child.stays) m f.1
  have root := (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared r.body m before).1
  exact ⟨⟨before,f.2⟩,⟨root,f.2⟩⟩

end Yulang.GeneralDeclarativeWitnessSelectedNonpointChild363
