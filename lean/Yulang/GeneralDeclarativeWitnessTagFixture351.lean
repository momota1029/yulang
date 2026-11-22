import Yulang.GeneralDeclarativeWitnessTagLocal351
import Yulang.GeneralDeclarativeTaggedFixtureModel340
import Yulang.GeneralDeclarativeWitnessOrderedFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessTagFixture351
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support)
open GeneralDeclarativeWitnessTagSources351 (Ref Script directBounds namedBounds)
open GeneralDeclarativeWitnessTagLocal351 (PatternData Route parse context next spans)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute decode Accepted)
open GeneralDeclarativeTaggedFixture340 (initial a d chosen registry eInt eBool whole fallback targets keep endState write)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativePlainFixture323 (source)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def span : Range := ⟨.interval 0,.interval 1⟩
def start : Table := ⟨initial.equations,[],[]⟩

def directContext : Option Context := do
  let ap ← attach initial start
  let bounds ← directBounds ap a 7 span ⟨0,.same⟩ ⟨1,.same⟩
  let parsedPlan ← parse catalogue interpretation source 7
  pure (context (r := registry) d chosen (.direct bounds) parsedPlan keep fallback targets)

def namedRaw : Expr := .join (.variable 3) (.variable 4)
def sourceLow : Equation := ⟨0,namedRaw⟩
def sourceUpper : Equation := ⟨2,namedRaw⟩
def firstArm : Equation := ⟨3,.variant 7 eInt⟩
def lastArm : Equation := ⟨4,.variant 7 eBool⟩
def original : State := ⟨initial.normal,[sourceLow,sourceUpper,firstArm,lastArm]⟩
def manifest : Table := ⟨[sourceLow,sourceUpper,firstArm],[(lastArm,19)],[19]⟩

def ref (n : Nat) : Ref := ⟨n,.same⟩
def follow : Script :=
  .join (.named (ref 2) .tagged) (.named (ref 3) .tagged)
def atLower : Script := .named (ref 0) follow
def atUpper : Script := .named (ref 1) follow

def knowsBoth (t : Table) (l h : Script) : Bool :=
  ((attach original t).map (fun a => (namedBounds a GeneralDeclarativeTaggedFixture340.a 7 span l h).isSome)).getD false

theorem named_source_exact : knowsBoth manifest atLower atUpper = true := by decide +kernel

theorem nested_named_not_literal :
    ((attach original manifest).map (fun table => (directBounds table a 7 span (ref 0) (ref 1)).isSome)).getD false
      = false := by decide +kernel

theorem withheld_arm : knowsBoth {manifest with released := []} atLower atUpper = false := by decide +kernel

theorem wrong_owner_arm :
    knowsBoth manifest (.named (ref 0) (.join (.named (ref 2) .tagged) (.named (ref 2) .tagged))) atUpper
      = false := by decide +kernel

theorem dropping_arm : knowsBoth manifest (.named (ref 0) (.named (ref 2) .tagged)) atUpper = false := by
  decide +kernel

structure Run where
  anchors : Attached original manifest
  bounds : GeneralDeclarativeWitnessTagSources351.NamedBounds anchors a 7
  parsed : PatternData catalogue interpretation source 7

def read : Option Run := do
  let table ← attach original manifest
  let paired ← namedBounds table a 7 span atLower atUpper
  let parsedPlan ← parse catalogue interpretation source 7
  pure ⟨table,paired,parsedPlan⟩

def Run.ctx (r : Run) : Context := context (r := registry) d chosen (.named r.bounds) r.parsed keep fallback targets

def namedRun : Option (Run × Finished) := do
  let r ← read
  let stages ← execute r.ctx
  pure (r,stages)

def writeFits (r : Run) (f : Finished) : Bool :=
  let slot := GeneralDeclarativeTaggedPatch340.captured original a 7 r.bounds.lower.payload r.bounds.upper.payload keep
  (decide (f.fixed = [⟨6,.variable slot.center⟩])) && f.kids.isEmpty

theorem genuine_named_write :
    (namedRun.map (fun (r,f) => writeFits r f)).getD false = true := by decide +kernel

theorem genuine_direct_write :
    ((directContext.bind execute).map (fun f => decide (f.fixed = [write]) && f.kids.isEmpty)).getD false = true := by
  decide +kernel

def checkedCompiler (r : Run) (f : Finished) (edited : List Equation → List Equation := id) :
    Bool := (do
  let plan ← literalPlan f.state f.state
  pure (decode r.ctx f.state ⟨[],edited f.fixed,plan⟩).isSome : Option Bool).getD false

theorem checked_named_compiler :
    (namedRun.map (fun (r,f) => checkedCompiler r f)).getD false = true := by decide +kernel

theorem wrong_symbolic_payload :
    (namedRun.map (fun (r,f) => checkedCompiler r f (fun _ => [⟨6,.variable 3⟩]))).getD true = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessTagFixture351
