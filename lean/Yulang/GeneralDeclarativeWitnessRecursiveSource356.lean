import Yulang.GeneralDeclarativeWitnessMixedLedger356
import Yulang.GeneralDeclarativeWitnessMixedFront356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecursiveSource356
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row Valuation)
open GeneralDeclarativeWitnessCovariantMetadata353 (Input)
open GeneralDeclarativeWitnessSpineFront355 (Site)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line AllParsed rebuild all printRow exact_list)
open GeneralDeclarativeWitnessRecursiveMixed356 (Plan Codes)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessMixedLedger356 (Packet Accepted Meaning returned_sound)
open GeneralDeclarativeWitnessRecursiveTree356 (dictionary)
open GeneralDeclarativeWitnessRecursiveSound356 (Evident)
open GeneralDeclarativeWitnessTypedRelease354 (Location)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)

mutual
inductive AuthorPlan where
  | typed (entered : Site) (children : AuthorPlans)
  | payload (clause binder : Nat)
inductive AuthorPlans where
  | nil
  | cons (head : AuthorPlan) (tail : AuthorPlans)
end

mutual
inductive ParsedPlan (cat : Input) : AuthorPlan → Plan → Type where
  | typed (head : AllParsed cat entered.rows body)
    (kids : ParsedPlans cat child checked) :
      ParsedPlan cat (.typed entered child) (.typed (entered.encode body) checked)
  | payload : ParsedPlan cat (.payload c b) (.ordinaryPayload c b)
inductive ParsedPlans (cat : Input) : AuthorPlans → List Plan → Type where
  | nil : ParsedPlans cat .nil []
  | cons : ParsedPlan cat first head → ParsedPlans cat more tail →
      ParsedPlans cat (.cons first more) (head::tail)
end

mutual
def parseOne (cat : Input) : (src : AuthorPlan) → Option (Σ q,ParsedPlan cat src q)
  | .typed entered children => do
    let ⟨rows,head⟩ ← all cat entered.rows
    let ⟨plans,kids⟩ ← parseList cat children
    pure ⟨.typed (entered.encode rows) plans,.typed head kids⟩
  | .payload c b => some ⟨.ordinaryPayload c b,.payload⟩
termination_by src => sizeOf src

def parseList (cat : Input) : (src : AuthorPlans) → Option (Σ q,ParsedPlans cat src q)
  | .nil => some ⟨[],.nil⟩
  | .cons one more => do
    let ⟨p,mapped⟩ ← parseOne cat one
    let ⟨ps,tail⟩ ← parseList cat more
    pure ⟨p::ps,.cons mapped tail⟩
termination_by src => sizeOf src
end

structure Source where
  base : Problem
  location : Location
  written : List Line
  environment : Scope
  author : AuthorPlans

structure Wire where
  root : GeneralDeclarativeWitnessCovariantInterval353.Wire
  out : GeneralDeclarativeWitnessTypedPacket354.Report
  children : Codes
  report : Packet

structure Found (p : Source) (s : State) (w : Wire) where
  root : Node s
  exactRoot : root.input = {p.base with rows := root.input.rows}
  written : AllParsed p.base.metadata p.written root.input.rows
  path : root.origin = p.location
  formed : List Plan
  authors : ParsedPlans p.base.metadata p.author formed
  replay : Accepted root p.environment w.report

def read (p : Source) (s : State) (w : Wire) : Option (Found p s w) :=
  match actual : rebuild p.base p.written with
  | none => none
  | some author => do
    let ⟨ps,preserved⟩ ← parseList p.base.metadata p.author
    let r ← GeneralDeclarativeWitnessTypedRangeWriter354.decode author.1 w.root s w.out
    let node : Node s := ⟨author.1,p.location,w.root,w.out,r⟩
    let retained ← GeneralDeclarativeWitnessMixedLedger356.read node p.environment ps w.children w.report
    pure ⟨node,GeneralDeclarativeWitnessCovariantFront353.unchanged actual,author.2,rfl,ps,preserved,retained⟩

theorem actual_authored_model {p s w} (a : Found p s w) (m : Assignment) (fit : Models s m) :
    a.root.input.rows.map printRow = p.written ∧
    w.report.answer.result = .selected (dictionary a.replay.proof) ∧
    w.report.answer.outputs = p.base.demand.outputs ∧
    (∀ entry ∈ w.report.outputs,Meaning m entry) ∧
    ∃ v : Valuation,Evident s m v p.base.demand (dictionary a.replay.proof) := by
  have exact := returned_sound a.replay m fit
  have same := congrArg Problem.demand a.exactRoot
  have certain : a.root.input.demand = p.base.demand := same
  obtain ⟨v,checked⟩ := exact.2.2.2.2
  exact ⟨exact_list a.written,exact.2.1,by simpa only [certain] using exact.2.2.1,
    exact.2.2.2.1,⟨v,certain ▸ checked⟩⟩

end Yulang.GeneralDeclarativeWitnessRecursiveSource356
