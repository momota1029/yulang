import Yulang.GeneralDeclarativeWitnessSelectedSourceMeaning363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 84000
set_option maxHeartbeats 108000000

namespace Yulang.GeneralDeclarativeWitnessTwoActualChildren363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessNonpointPort362 (author frame whereSource receiver)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (asked)
open GeneralDeclarativeWitnessBackedNativeInput363 (Backed verify source_evidence_agrees_in_every_model)
open GeneralDeclarativeWitnessNonpointGraph363 (Safe graph graph_exact_positive)
open GeneralDeclarativeWitnessLocatedElection363 (Chosen choose exact_compiler_must_use_chosen_row election_not_called_from_compiler)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Query rootQuery)
open GeneralDeclarativeWitnessNativeInstall360 (Fits World NativeViews)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context same_model_of_prepared)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeWitnessCompiler350 (Finished execute portNames printDemand trip)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration Clause)

def secondClause : Clause := {whereSource with id := 192, role := 15}
def parent : Declaration := {author with requirements := [whereSource,secondClause]}
def secondReceiver : Declaration := {receiver with id := 100, role := 15}
def environment : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨10,2,[]⟩,⟨11,1,[]⟩,⟨15,1,[]⟩]⟩,
    declarations := [parent,receiver,secondReceiver]}
def f1 : FrameKey := ⟨[10,0],98,1⟩
def f2 : FrameKey := ⟨[10,1],100,2⟩
def wrong : FrameKey := ⟨[10,1],100,1⟩

def rootLayout (w : World) {e : Environment} (c : Chosen e asked frame) : Layout :=
  {GeneralDeclarativeWitnessCrossOwnerReceiver362.layout w with spans := c.fitBare.captures}

def childLayout (w : World) {e : Environment} {f : FrameKey} {d : Demand} (c : Chosen e d f) : Layout :=
  ⟨w.ordinary,c.fitBare.captures,[60,61,62,201,202,203],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Leaf (e : Environment) (w : World) (d : Demand) (f : FrameKey) (port : Capture) where
  input : d.arguments = [port]
  graphSource : Safe w
  chosen : Chosen e d f
  prepared : Prepared e f d (childLayout w chosen)
  agrees : prepared.impl = chosen.impl
  bound : Capture
  stored : slots [prepared.captures] f 92 = some bound
  centered : bound.center = port.center
  body : Finished
  compiled : execute (context e d prepared.impl (childLayout w chosen)) = some body
  keeps : preserves w.ordinary body.state = true
  noWrites : body.fixed = []
  noKids : body.kids = []

def Leaf.world {e w d f p} (l : Leaf e w d f p) : World := ⟨l.body.state,w.board⟩

def readLeaf (e : Environment) (w : World) (d : Demand) (f : FrameKey) (p : Capture)
    (input : d.arguments = [p]) : Option (Leaf e w d f p) := do
  if h : graph w then
    let c ← choose e d f
    let b ← prepare e f d (childLayout w c)
    match had : slots [b.captures] f 92 with
    | none => none
    | some port =>
      if center : port.center = p.center then
        match ran : execute (context e d b.impl (childLayout w c)) with
        | none => none
        | some result =>
          if good : preserves w.ordinary result.state = true ∧ result.fixed = [] ∧ result.kids = [] then
            some ⟨input,graph_exact_positive h,c,b,exact_compiler_must_use_chosen_row c b,
              port,had,center,result,ran,good.1,good.2.1,good.2.2⟩
          else none
      else none
  else none

theorem Leaf.prior {e w d f p} (r : Leaf e w d f p) (m : Assignment) (v : NativeViews) (fit : Fits r.world m v) :
    Fits w m v := ⟨restrict ((preserves_iff ..).mp r.keeps) m fit.1,fit.2⟩

structure Pair {contra : Bool} (x : Ordered contra) where
  env : Environment
  ready : Backed x env
  graphSource : Safe x.after.final
  chosen : Chosen env asked frame
  body : Prepared env frame asked (rootLayout x.after.final chosen)
  same : body.impl = chosen.impl
  authored : body.impl = parent
  first : Demand
  second : Demand
  ordered : body.kids = [first,second]
  port : Capture
  actualPort : port =
    (portNames (context env asked body.impl (rootLayout x.after.final chosen)) body.ports).input 90
  a : Leaf env ⟨body.stage,x.after.final.board⟩ first f1 port
  b : Leaf env a.world second f2 port

def build {contra} (x : Ordered contra) : Option (Pair x) := do
  let e ← environment
  let backing ← verify x e
  if safe : graph x.after.final then
    let c ← choose e asked frame
    let body ← prepare e frame asked (rootLayout x.after.final c)
    if authors : body.impl = parent then
      match literal : body.kids with
      | [a,b] =>
        let port := (portNames (context e asked body.impl (rootLayout x.after.final c)) body.ports).input 90
        have exactArgs : [a.arguments,b.arguments] = [[port],[port]] := by
          have h := congrArg (List.map Demand.arguments) literal
          simpa [port,Prepared.kids,GeneralDeclarativeEmissionForest322.children,authors,parent,whereSource,secondClause,
            GeneralDeclarativeSourceEmission322.demand,GeneralDeclarativeSourceEmission322.inputs,
            GeneralDeclarativeSourceEmission322.useArg,GeneralDeclarationPatterns.normalize] using h.symm
        have args : a.arguments = [port] ∧ b.arguments = [port] := by simpa using exactArgs
        let l ← readLeaf e ⟨body.stage,x.after.final.board⟩ a f1 port args.1
        let r ← readLeaf e l.world b f2 port args.2
        some ⟨e,backing,graph_exact_positive safe,c,body,exact_compiler_must_use_chosen_row c body,
          authors,a,b,literal,port,rfl,l,r⟩
      | _ => none
    else none
  else none

def checked {contra x} (p : @Pair contra x) : Bool :=
  decide (p.chosen.impl.id = 97 ∧ p.a.chosen.impl.id = 98 ∧ p.b.chosen.impl.id = 100 ∧
    p.body.impl.requirements.map Clause.id = [191,192] ∧
    p.body.kids.map printDemand = [(11,[(310,302,311)],[]),(15,[(310,302,311)],[])] ∧
    trip p.a.bound = (314,302,315) ∧ trip p.b.bound = (316,302,317)) &&
  (choose p.env p.second wrong).isNone

theorem two_distinct_ordered_literal_children (contra : Bool) :
    ((run contra).bind fun x => (build x).map checked).getD false = true := by
  cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessTwoActualChildren363
