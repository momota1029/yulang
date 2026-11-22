import Yulang.GeneralDeclarativeWitnessTypedForest354
import Yulang.GeneralDeclarativeWitnessCovariantFront353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedSource354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessCovariantMetadata353 (Input)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line AllParsed rebuild all printRow exact_list)
open GeneralDeclarativeWitnessTypedForest354 (Plan Wire Accepted BackedNode)
open GeneralDeclarativeWitnessTypedRelease354 (Location Authority)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

structure SourcePlan where
  ordinal : Nat
  lines : List Line
  keep : List Nat
  fallback : Nat → Capture

def SourcePlan.encode (p : SourcePlan) (rows : List GeneralDeclarativeWitnessCovariantOrigin353.Row) : Plan :=
  ⟨p.ordinal,rows,p.keep,p.fallback⟩

inductive Written (catalogue : Input) : List SourcePlan → List Plan → Type where
  | nil : Written catalogue [] []
  | cons (read : AllParsed catalogue p.lines rows) :
    Written catalogue ps compiled → Written catalogue (p::ps) (p.encode rows::compiled)

def writePlans (catalogue : Input) : (ps : List SourcePlan) → Option (Σ qs, Written catalogue ps qs)
  | [] => some ⟨[],.nil⟩
  | p :: more => do
    let ⟨rows,checked⟩ ← all catalogue p.lines
    let ⟨qs,rest⟩ ← writePlans catalogue more
    pure ⟨p.encode rows :: qs,.cons checked rest⟩

theorem all_authored {m p q} (w : Written m p q) :
    q.map (fun x => x.authored.map printRow) = p.map SourcePlan.lines := by
  induction w with
  | nil => rfl
  | cons h rest ih => simp only [List.map_cons,SourcePlan.encode,exact_list h,ih]

theorem original_only {m p q} (w : Written m p q) :
    q.map Plan.writtenOrdinal = p.map SourcePlan.ordinal := by
  induction w with
  | nil => rfl
  | cons _ rest ih => simp only [List.map_cons,SourcePlan.encode,ih]

structure Source where
  producer : Problem
  location : Location
  authority : Authority
  written : List Line
  children : List SourcePlan

structure Verified (p : Source) (s : State) (w : Wire) where
  compiled : GeneralDeclarativeWitnessTypedForest354.Input
  producer : compiled.producer = {p.producer with rows := compiled.producer.rows}
  written : AllParsed p.producer.metadata p.written compiled.producer.rows
  ordered : Written p.producer.metadata p.children compiled.kids
  path : compiled.location = p.location
  authority : compiled.authority = p.authority
  actual : Accepted compiled s w

def decode (p : Source) (s : State) (w : Wire) : Option (Verified p s w) :=
  match typed : rebuild p.producer p.written with
  | none => none
  | some source => do
    let ⟨read,checked⟩ ← writePlans p.producer.metadata p.children
    let i : GeneralDeclarativeWitnessTypedForest354.Input := ⟨source.1,p.location,p.authority,read⟩
    let linked ← GeneralDeclarativeWitnessTypedForest354.decode i s w
    pure ⟨i,GeneralDeclarativeWitnessCovariantFront353.unchanged typed,source.2,checked,rfl,rfl,linked⟩

theorem not_solver_rows {p s w} (v : Verified p s w) :
    v.compiled.producer.rows.map printRow = p.written ∧
    v.compiled.kids.map (fun q => q.authored.map printRow) = p.children.map SourcePlan.lines ∧
    v.compiled.kids.map Plan.writtenOrdinal = p.children.map SourcePlan.ordinal :=
  ⟨exact_list v.written,all_authored v.ordered,original_only v.ordered⟩

theorem scoped_same_model {p s w} (v : Verified p s w) (m : Assignment) (fit : Models s m) :
    w.report.result = .selected (.node v.actual.parent.output.source.decl.id v.actual.children.dicts) ∧
    w.report.outputs = p.producer.demand.outputs ∧
    All₂ (BackedNode s m) v.actual.parent.output.children v.actual.children.dicts := by
  have report := GeneralDeclarativeWitnessTypedForest354.exact_model v.actual m fit
  have source := congrArg Problem.demand v.producer
  exact ⟨report.1,by simpa only [source] using report.2.1,report.2.2.1⟩

end Yulang.GeneralDeclarativeWitnessTypedSource354
