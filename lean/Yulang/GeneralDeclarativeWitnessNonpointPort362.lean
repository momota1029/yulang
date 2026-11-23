import Yulang.GeneralDeclarativeWitnessNativeWindowWitness362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 69000
set_option maxHeartbeats 72000000
namespace Yulang.GeneralDeclarativeWitnessNonpointPort362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (Opened read)
open GeneralDeclarativeWitnessNativeOrder362 (Chain chain)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (Fits World NativeViews)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessCompiler350 (printDemand portNames)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration Clause)
open GeneralNominalCommonBridge (Assignment)

def requestWindow : Capture := ⟨201,202,203⟩
def ordinary : Capture := ⟨60,61,62⟩
def frame : FrameKey := ⟨[10],97,0⟩
def whereSource : Clause := ⟨191,11,[.var 90],[]⟩
def author : Declaration := ⟨97,10,[.var 90,.var 91],[whereSource],[],[]⟩
def receiver : Declaration := ⟨98,11,[.var 92],[],[],[]⟩
def env : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨10,2,[]⟩,⟨11,1,[]⟩]⟩,
    declarations := [author,receiver]}

def request : Demand := ⟨10,[requestWindow,ordinary],[]⟩

def layout (w : World) : Layout :=
  ⟨w.ordinary,[(90,requestWindow),(91,ordinary)],[60,61,62,201,202,203],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Transport {contra : Bool} (r : Run contra) (gate : ReleaseAuthority) where
  inputs : Opened r gate
  lowerTarget : r.lower.write.address.target = requestWindow.lower
  centerTarget : r.center.write.address.target = requestWindow.center
  upperTarget : r.upper.write.address.target = requestWindow.upper
  environment : Environment
  source : Prepared environment frame request (layout r.final)
  sameAuthor : source.impl = author
  child : Demand
  generated : source.kids = [child]
  fromActualBinder : child.arguments =
    [(portNames (context environment request source.impl (layout r.final)) source.ports).input 90]

/-- Certify three different granted input addresses, then replay the
actual authored where body. This consumes one nonpoint input, not three
projections of a single point. It is not a general election algorithm. -/
def forward {contra} (r : Run contra) (gate : ReleaseAuthority) : Option (Transport r gate) := do
  let inputs ← read r gate
  if targets : r.lower.write.address.target = requestWindow.lower ∧
      r.center.write.address.target = requestWindow.center ∧ r.upper.write.address.target = requestWindow.upper then
    let e ← env
    let p ← prepare e frame request (layout r.final)
    if same : p.impl = author then
      match children : p.kids with
      | [child] =>
        have actual : child.arguments =
            [(portNames (context e request p.impl (layout r.final)) p.ports).input 90] := by
          have ids := congrArg (List.map Demand.arguments) children
          simpa [Prepared.kids,GeneralDeclarativeEmissionForest322.children,same,author,whereSource,
              GeneralDeclarativeSourceEmission322.demand,GeneralDeclarativeSourceEmission322.inputs,
              GeneralDeclarativeSourceEmission322.useArg,GeneralDeclarationPatterns.normalize] using ids.symm
        some ⟨inputs,targets.1,targets.2.1,targets.2.2,e,p,same,child,children,actual⟩
      | _ => none
    else none
  else none

def Transport.world {contra r gate} (p : @Transport contra r gate) : World :=
  ⟨p.source.stage,r.final.board⟩

def inspect {contra r gate} (p : @Transport contra r gate) : Bool :=
  decide (printDemand p.child = (11,[(210,202,211)],[]))

theorem actual_child_has_distinct_logical_endpoints (contra : Bool) :
    ((run contra).bind fun r => (forward r authority).map inspect).getD false = true := by
  cases contra <;> decide +kernel

inductive Part | lower | center | upper

def target : Part → Nat
  | .lower => requestWindow.lower
  | .center => requestWindow.center
  | .upper => requestWindow.upper

def view (views : NativeViews) (which : Part) := views (target which)

theorem current_child_projection_keeps_all_three_sources {contra} {r : Run contra} {gate}
    (p : Transport r gate) (m : Assignment) (v : NativeViews) (fit : Fits p.world m v) :
    view v .lower = some (r.lower.write.code.eval m) ∧
    view v .center = some (r.center.write.code.eval m) ∧
    view v .upper = some (r.upper.write.code.eval m) := by
  have prior : Fits r.final m v :=
    ⟨(GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared p.source m fit.1).1,fit.2⟩
  obtain ⟨lo,mid,hi⟩ := GeneralDeclarativeWitnessOrderedNativeRelease362.exact_current_values p.inputs m v prior
  exact ⟨by simpa only [view,target,p.lowerTarget] using lo,
    by simpa only [view,target,p.centerTarget] using mid,
    by simpa only [view,target,p.upperTarget] using hi⟩

end Yulang.GeneralDeclarativeWitnessNonpointPort362
