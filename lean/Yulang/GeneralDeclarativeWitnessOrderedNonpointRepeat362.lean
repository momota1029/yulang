import Yulang.GeneralDeclarativeWitnessReaderModeAgreement362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 70000
set_option maxHeartbeats 78000000
namespace Yulang.GeneralDeclarativeWitnessOrderedNonpointRepeat362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (Opened read)
open GeneralDeclarativeWitnessNonpointPort362 (layout frame request author whereSource receiver)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand trip)
open GeneralDeclarativeWitnessLiteral349 (preserves)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)

def secondClause := {whereSource with id := 192}
def twice : Declaration := {author with requirements := [whereSource,secondClause]}

def env : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨10,2,[]⟩,⟨11,1,[]⟩]⟩,declarations := [twice,receiver]}

def key (i : Nat) : FrameKey := ⟨[10,i],98,1⟩

def receiverLayout (w : World) (cap : Capture) : Layout :=
  ⟨w.ordinary,[(92,cap)],[60,61,62,201,202,203],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Body (e : Environment) (w : World) (d : Demand) (i : Nat) where
  passed : Capture
  args : d.arguments = [passed]
  chosen : Prepared e (key i) d (receiverLayout w passed)
  actual : chosen.impl = receiver
  span : Capture
  boundScope : slots [chosen.captures] (key i) 92 = some span
  centered : span.center = passed.center
  result : Finished
  executed : execute (context e d chosen.impl (receiverLayout w passed)) = some result
  keeps : preserves w.ordinary result.state = true
  noWrites : result.fixed = []
  noChildren : result.kids = []

def Body.world {e w d i} (r : Body e w d i) : World := ⟨r.result.state,w.board⟩

def replay (e : Environment) (w : World) (d : Demand) (i : Nat) : Option (Body e w d i) := do
  match requested : d.arguments with
  | [span] =>
    let p ← prepare e (key i) d (receiverLayout w span)
    if actual : p.impl = receiver then
      match routed : slots [p.captures] (key i) 92 with
      | none => none
      | some cap =>
        if exact : cap.center = span.center then
          match evaluated : execute (context e d p.impl (receiverLayout w span)) with
          | none => none
          | some result =>
            if kit : preserves w.ordinary result.state = true ∧ result.fixed = [] ∧ result.kids = [] then
              some ⟨span,requested,p,actual,cap,routed,exact,result,evaluated,kit.1,kit.2.1,kit.2.2⟩
            else none
        else none
    else none
  | _ => none

structure PairOfBodies {contra : Bool} (r : Run contra) where
  granted : Opened r authority
  env : Environment
  parent : Prepared env frame request (layout r.final)
  literal : parent.impl = twice
  firstChild : Demand
  nextChild : Demand
  compiled : parent.kids = [firstChild,nextChild]
  first : Body env ⟨parent.stage,r.final.board⟩ firstChild 0
  last : Body env first.world nextChild 1

/-- The exact second where receipt is replayed on the first returned
state. Two equal request descriptions are not two equal source scopes. -/
def produce {contra} (r : Run contra) : Option (PairOfBodies r) := do
  let auth ← read r authority
  let e ← env
  let source ← prepare e frame request (layout r.final)
  if own : source.impl = twice then
    match actual : source.kids with
    | [a,b] =>
      let first ← replay e ⟨source.stage,r.final.board⟩ a 0
      let after ← replay e first.world b 1
      pure ⟨auth,e,source,own,a,b,actual,first,after⟩
    | _ => none
  else none

def exact {contra r} (p : @PairOfBodies contra r) : Bool :=
  decide (p.parent.impl.requirements.map GeneralDeclarations.Clause.id = [191,192] ∧
    p.parent.kids.map printDemand = [(11,[(210,202,211)],[]),(11,[(210,202,211)],[])] ∧
    trip p.first.span = (214,202,215) ∧ trip p.last.span = (216,202,217)) &&
  ((slots [p.first.chosen.captures,p.last.chosen.captures] (key 0) 92).map trip == some (214,202,215)) &&
  ((slots [p.first.chosen.captures,p.last.chosen.captures] (key 1) 92).map trip == some (216,202,217)) &&
  ((slots [p.first.chosen.captures,p.last.chosen.captures] (key 2) 92).isNone)

theorem actual_two_scopes_share_exact_center_not_alias_addresses (contra : Bool) :
    ((run contra).bind fun r => (produce r).map exact).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessOrderedNonpointRepeat362
