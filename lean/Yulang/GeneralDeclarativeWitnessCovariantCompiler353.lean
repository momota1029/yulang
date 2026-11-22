import Yulang.GeneralDeclarativeWitnessCovariantOrigin353
import Yulang.GeneralDeclarativeWitnessCovariantDescent353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantCompiler353
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Anchored read ModelsAt assigned whole_full actual_center)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open GeneralDeclarativeWitnessCovariant352 (matchBindings)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeWitnessCompiler350 (Context Accepted printDemand)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def declarations {p : Problem} {w : Wire} (a : Anchored p w) : List Declaration :=
  a.metadataProof.source.declarations.filter (fun d => d.role == p.demand.role)

def selectedSlot {p : Problem} {w : Wire} (a : Anchored p w) : Capture :=
  ⟨a.current.valueName,a.current.valueName,a.current.valueName⟩

def captures {p : Problem} {w : Wire} (a : Anchored p w) (names : List Nat) : List (Nat × Capture) :=
  names.map fun n => (n,selectedSlot a)

theorem whole_in_each {p : Problem} {w : Wire} (a : Anchored p w) (ns : List Nat)
    (m : Assignment) (fit : Models p.stage m) :
    ∀ span ∈ captures a ns, Equivalent (m span.2.center).1
      (.union (m a.first.valueName).1 (m a.last.valueName).1) := by
  intro span used
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp used
  exact whole_full a m fit

structure Prepared (p : Problem) (w : Wire) where
  anchor : Anchored p w
  decl : Declaration
  only : declarations anchor = [decl]
  written : decl.head = [w.written]
  good : GeneralDeclarativeWitnessCovariantDescent353.legal anchor.metadataProof.source decl = true
  declaredRoot : GeneralDeclarativeWitnessProblem349.declared anchor.metadataProof.source p.demand = true
  names : List Nat
  binds : names = decl.inputNames

def prepare (p : Problem) (w : Wire) : Option (Prepared p w) := do
  let a ← read p w
  match hit : declarations a with
  | [d] =>
    if written : d.head = [w.written] then
      if declOK : GeneralDeclarativeWitnessCovariantDescent353.legal a.metadataProof.source d = true then
        if defined : GeneralDeclarativeWitnessProblem349.declared a.metadataProof.source p.demand = true then do
          let b ← matchBindings a.shape.pattern a.shape.tag a.shape.box
          if ids : b.names = d.inputNames then some ⟨a,d,hit,written,declOK,defined,b.names,ids⟩ else none
        else none
      else none
    else none
  | _ => none

def Prepared.ctx {p : Problem} {w : Wire} (a : Prepared p w) : Context :=
  let s := a.anchor.metadataProof.source
  ⟨registry s,interpretation s.snapshot,p.demand,a.decl,p.stage,
    captures a.anchor a.names,p.keep,p.fallback,p.targets⟩

structure Checked (p : Problem) (w : Wire) (current : State) (out : GeneralDeclarativeWitnessCompiler350.Wire) where
  prepared : Prepared p w
  kept : preserves p.stage current = true
  receipt : Accepted prepared.ctx current out

def check (p : Problem) (w : Wire) (current : State)
    (out : GeneralDeclarativeWitnessCompiler350.Wire) : Option (Checked p w current out) := do
  let before ← prepare p w
  if kept : preserves p.stage current = true then do
    let receipt ← GeneralDeclarativeWitnessCompiler350.decode before.ctx current out
    pure ⟨before,kept,receipt⟩
  else none

theorem retained {p : Problem} {w : Wire} {s : State} {out}
    (a : Checked p w s out) (m : Assignment) (fit : Models s m) : Models p.stage m :=
  GeneralDeclarativeGrowth327.restrict ((preserves_iff ..).mp a.kept) m fit

/-- Connect the independent typed head and its exact ordinary payload
span to the unmodified body compiler. No full old-carrier nominal head
or old Classify verdict is claimed. -/
theorem confirmed {p : Problem} {w : Wire} {s : State} {out}
    (a : Checked p w s out) (m : Assignment) (fit : Models s m) :
    (∀ pair ∈ a.prepared.ctx.spans, Equivalent (m pair.2.center).1
      (.union (m a.prepared.anchor.first.valueName).1 (m a.prepared.anchor.last.valueName).1)) ∧
    out.children = a.receipt.compiled.kids.map printDemand ∧
    out.outputRows.map Equation.left = p.demand.outputs.map GeneralSourceState.Output.target ∧
    (∀ e ∈ out.outputRows,Holds m e) := by
  exact ⟨whole_in_each a.prepared.anchor a.prepared.names m (retained a m fit),a.receipt.printed,
    GeneralDeclarativeWitnessCompiler350.fixed_in_current a.receipt m fit⟩

end Yulang.GeneralDeclarativeWitnessCovariantCompiler353
