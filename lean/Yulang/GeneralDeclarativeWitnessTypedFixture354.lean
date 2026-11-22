import Yulang.GeneralDeclarativeWitnessTypedChild354
import Yulang.GeneralDeclarativeWitnessCovariantFixture353
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 38000
set_option maxHeartbeats 28000000
namespace Yulang.GeneralDeclarativeWitnessTypedFixture354
open GeneralDeclarativeWitnessCovariantFixture353 (parent input source stage wire clause0 eInt eBool)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessTypedPacket354 (Run Report run)
open GeneralDeclarativeWitnessTypedRelease354 (Location Authority Key Stamp)
open GeneralDeclarativeWitnessTypedChild354 (Input Wire downstream decode)
open GeneralDeclarativeWitnessCompiler350 (execute printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessCovariantHead352 (rawPattern)

def decl : Declaration :=
  {parent with requirements := [clause0], associated :=
    [⟨91,0,.variant 13 (.app 0 [.var 31])⟩,⟨95,1,.var 32⟩]}
def receiver : Declaration := ⟨93,3,[rawPattern],[],[],[]⟩

def actualRoot : Demand := ⟨1,[⟨20,20,20⟩],[⟨0,9⟩,⟨1,6⟩]⟩
def producer : Problem :=
  let original := GeneralDeclarativeWitnessCovariantFixture353.problem
  let mutableInput := {input with declarations := [decl,receiver]}
  let metaInput := {original.metadata with sourceInput := mutableInput}
  {original with metadata := metaInput, demand := actualRoot}
def authored : List Row :=
  [⟨30,13,0,7⟩,⟨31,13,0,8⟩,⟨32,13,0,32⟩,⟨33,13,0,33⟩]

def loc : Location := ⟨[4],7⟩
def active : Stamp := ⟨[4],1,92,7⟩
def key : Key := ⟨active,0,0,9⟩
def authority : Authority := ⟨[active],[key]⟩
def problem : Input := ⟨producer,loc,authority,0,0,authored,[49],fun _ => ⟨9,9,9⟩⟩

def writtenRow : Row := ⟨9,13,0,9⟩
def childHead : GeneralDeclarativeWitnessCovariantInterval353.Wire :=
  ⟨⟨0,rawPattern,0,1,authored.length⟩,2,3,.constraint 2,.constraint 5⟩

def data : Option (State × Wire) := do
  let top ← run producer wire
  let kid ← top.children[0]?
  let a ← GeneralDeclarativeWitnessTypedPacket354.typedAt top.writes 0
  let seed := downstream problem top.state kid a.1.typed.row
  let facts ← GeneralDeclarativeWitnessCovariantInterval353.read seed childHead
  let leaf ← execute facts.ctx
  let current := leaf.state
  let prior ← literalPlan top.state current
  let retain ← literalPlan leaf.state current
  pure (current,⟨wire,⟨top.source.decl.id,top.children.map printDemand,top.writes.trace,prior⟩,
    childHead,⟨leaf.kids.map printDemand,leaf.fixed,retain⟩⟩)

def test (i : Input := problem) (edit : Wire → Wire := id) : Bool :=
  (data.map (fun (s,w) => (decode i s (edit w)).isSome)).getD false

theorem accepted : test = true := by decide +kernel

theorem real_output_order :
    (data.map (fun (_,w) => decide (w.writer.trace = [.typed writtenRow,.ordinary ⟨6,.variable 9⟩]))).getD false =
      true := by decide +kernel

theorem actual_where_child :
    (data.map (fun (_,w) => decide (w.writer.kids = [(3,[(32,9,33)],[])]))).getD false = true := by decide +kernel

theorem old_fixed_not_the_new_output :
    ((run producer wire).map fun a =>
      (GeneralDeclarativeWitnessCompiler350.fixedBatch a.source.ctx a.ports).isNone).getD false = true := by
  decide +kernel

theorem no_release : test {problem with auth := {authority with released := []}} = false := by decide +kernel

theorem wrong_path :
    test {problem with auth := {authority with released := [{key with stamp := {active with path := [5]}}]}} = false := by
  decide +kernel

theorem wrong_version :
    test {problem with auth := {authority with released := [{key with stamp := {active with version := 6}}]}} = false := by
  decide +kernel

theorem wrong_write_ordinal : test {problem with writeOrdinal := 1} = false := by decide +kernel

theorem wrong_child_ordinal : test {problem with childOrdinal := 1} = false := by decide +kernel

theorem wrong_output_target :
    test {problem with auth := {authority with released := [{key with target := 6}]}} = false := by decide +kernel

theorem swapped_outputs :
    test problem (fun w => {w with writer := {w.writer with trace := w.writer.trace.reverse}}) = false := by decide +kernel

theorem wrong_nominal :
    test problem (fun w => {w with writer := {w.writer with trace :=
      [.typed {writtenRow with box := 1},.ordinary ⟨6,.variable 9⟩]}}) = false := by decide +kernel

theorem cannot_call_output_authored :
    test {problem with authored := authored ++ [writtenRow]} = false := by decide +kernel

theorem two_incarnations :
    test {problem with auth := {authority with active := [active,{active with version := 6}]}} = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTypedFixture354
