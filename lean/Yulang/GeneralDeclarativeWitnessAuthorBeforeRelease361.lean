import Yulang.GeneralDeclarativeWitnessAuthorOrdinaryChoice361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 68000000
namespace Yulang.GeneralDeclarativeWitnessAuthorBeforeRelease361
open GeneralDeclarativeWitnessAuthorOrdinaryChoice361 (Author OrdinaryChild author_checked child_checked aligned)
open GeneralDeclarativeWitnessNestedInstall360 (Run layout requested)
open GeneralDeclarativeWitnessNativeBodyFixture360 (childDecl)
open GeneralDeclarativeWitnessMixedForwardChoice361
open GeneralDeclarativeWitnessNestedFixture361 (receiver)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared prepare context)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)
open GeneralDeclarativeWitnessNativePipeline360 (wire gate authority)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessNativeRelease360 (checkExactRelease)
open GeneralDeclarativeWitnessNestedOrdered360 (Child)
open GeneralDeclarativeWitnessOrderedChild360 (childKey childLayout)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessReleasedForward360 (forwardKey forwardDemand fixed)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessLiteral349 (preserves)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)

def source (negative : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,2,[]⟩,⟨8,1,[]⟩]⟩,
    declarations := [GeneralDeclarativeWitnessAuthorOrdinaryChoice361.aligned negative,childDecl,
      GeneralDeclarativeWitnessMixedForwardChoice361.aligned,receiver negative false]}

structure Started (negative : Bool) where
  root : Run negative
  approved : Author root.env negative
  exact : root.prep.impl = GeneralDeclarativeWitnessAuthorOrdinaryChoice361.aligned negative

def start (negative : Bool) : Option (Started negative) := do
  let env ← source negative
  if validated : Author.check env negative then
    let decision := author_checked validated
    let p ← prepare env parentScope requested layout
    let result ← GeneralDeclarativeWitnessNativeValue360.compile p table (wire negative) 3
    match saved : commit p result ⟨layout.named,gate⟩ with
    | none => none
    | some final =>
      some ⟨⟨env,p,result,final,saved⟩,decision,Option.some.inj (p.authored.symm.trans decision.atSource)⟩
  else none

/-- Ordinary child replay contains no release predicate or native lookup.
The ledger may contain the preinstalled value but it is not consulted. -/
structure Prefix {negative : Bool} (r : Run negative) where
  asked : Demand
  exactChild : r.prep.kids = [asked]
  span : Capture
  args : asked.arguments = [span]
  found : OrdinaryChild r asked
  prepared : Prepared r.env childKey asked (childLayout r.final span)
  actualSource : prepared.impl = childDecl
  result : Finished
  actual : execute (context r.env asked prepared.impl (childLayout r.final span)) = some result
  noKids : result.kids = []
  keeps : preserves r.final.ordinary result.state = true

def beforeGrant {negative} (r : Run negative) : Option (Prefix r) :=
  match kids : r.prep.kids with
  | [d] =>
    match args : d.arguments with
    | [span] =>
      if checked : OrdinaryChild.check r d then do
        let selected := child_checked checked
        let p ← prepare r.env childKey d (childLayout r.final span)
        match actual : execute (context r.env d p.impl (childLayout r.final span)) with
        | none => none
        | some f =>
          if exact : f.kids = [] ∧ preserves r.final.ordinary f.state = true then
            have source : p.impl = childDecl := Option.some.inj (p.authored.symm.trans selected.atSource)
            some ⟨d,kids,span,args,selected,p,source,f,actual,exact.1,exact.2⟩
          else none
      else none
    | _ => none
  | _ => none

structure Continued {negative : Bool} {r : Run negative} (p : Prefix r) where
  actual : Sequence r
  sameBody : actual.ordinaryChild.result = p.result

/-- The certificate now checks the independent live grant after replaying
the selected ordinary where clause; grant creation is not inferred. -/
def close {negative} {r : Run negative} (p : Prefix r) : Option (Continued p) := do
  let opened ← checkExactRelease r.final.board authority r.typed.write
  let actualChild : Child r := ⟨p.asked,p.exactChild,p.span,p.args,opened,p.prepared,p.result,p.actual,p.noKids,p.keeps⟩
  let retained ← checkExactRelease actualChild.final.board authority r.typed.write
  let continuation ← prepare r.env forwardKey forwardDemand (fixed actualChild.final)
  match compiled : continuation.kids with
  | [receiver] =>
    match a : receiver.arguments with
    | [port] =>
      if center : port.center = r.typed.write.address.target then
        some ⟨⟨actualChild,retained,continuation,receiver,compiled,port,a,center⟩,rfl⟩
      else none
    | _ => none
  | _ => none

end Yulang.GeneralDeclarativeWitnessAuthorBeforeRelease361
