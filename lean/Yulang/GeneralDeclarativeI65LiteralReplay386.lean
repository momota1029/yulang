import Yulang.GeneralDeclarativeI65SourceEventTrace381
import Yulang.GeneralDeclarativeWitnessTree349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Frontier Tree Resolves)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralSourceState (Output)
open CommonRecursiveNominalIntervals (Argument)

/-- Literal output syntax, not interpretation on a model. A declared
body retains its whole syntax and the ordered value/row argument
vector (arbitrary arity and both point and nonpoint components).
The ordinary case retains the exact written ordinary equation. -/
inductive LiteralWriteSyntax where
  | ordinary (row : GeneralDeclarativeHead320.Equation)
  | declared (target : Nat) (sourceSyntax : Pattern) (arguments : List (Argument Nat))

structure OrderedReceipt where
  occurrence : List Nat
  ordinal : Nat
  requested : Output
  source : Body
  written : LiteralWriteSyntax

def OrderedReceipt.writesTarget (receipt : OrderedReceipt) : Prop :=
  match receipt.written with
  | .ordinary equation => equation.left = receipt.requested.target
  | .declared target _ _ => target = receipt.requested.target

/-- The original where clause, not the identity of a physically
installed child. Its position is witnessed in the enclosing event. -/
structure LiteralWhereEntry where
  clause : Clause
  demand : Demand

/-- Proof data of a literal selected source occurrence. Its source
rule is outside this structural carrier and must justify this very
event. The carrier itself does not prove an occurrence is selected. -/
structure LiteralLocalEvent (s : State) (q : Request) where
  declarationOrdinal : Nat
  declaration : Declaration
  declaredAt : (authoredRegistry s.current).declarations[declarationOrdinal]? = some declaration
  inScope : declaration ∈ visible s q
  captures : List (Nat × Capture)
  whereEntries : List LiteralWhereEntry
  whereCount : whereEntries.length = declaration.requirements.length
  whereAt : ∀ (i : Nat) entry, whereEntries[i]? = some entry →
    declaration.requirements[i]? = some entry.clause ∧ entry.demand.role = entry.clause.role
  receipts : List OrderedReceipt
  receiptCount : receipts.length = q.demand.outputs.length
  receiptAt : ∀ (i : Nat) receipt, receipts[i]? = some receipt →
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
    q.demand.outputs[i]? = some receipt.requested ∧
    Supplies (authoredRegistry s.current).roles declaration receipt.requested.name receipt.source ∧
    receipt.writesTarget

def LiteralLocalEvent.kids {s q} (event : LiteralLocalEvent s q) : List Request :=
  children q (event.whereEntries.map LiteralWhereEntry.demand)

abbrev LiteralEvent (s : State) := Sigma (LiteralLocalEvent s)

/-- The still independent local source judgment and its data-level
event relation. Structural replay works uniformly for this interface
and does not supply or choose its language rules. -/
class ReplayJudgment where
  localRule : State → Request → Frontier Request → Prop
  eventAt : ∀ {s q key kids}, localRule s q (.selected key kids) →
    LiteralLocalEvent s q → Prop

abbrev LocalSource [judgment : ReplayJudgment] := judgment.localRule

inductive LiteralTraceRule (judgment : ReplayJudgment) (s : State) :
    Request → Frontier Request → LiteralEvent s → Prop where
  | selected (event : LiteralLocalEvent s q)
      (proved : judgment.localRule s q (.selected event.declaration.id event.kids))
      (same : judgment.eventAt proved event) :
      LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩

mutual
inductive GeneralTree [judgment : ReplayJudgment] (s : State) : Request → Dictionary → List OrderedReceipt → Type where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩) :
      GeneralForest s event.kids ds later →
      GeneralTree s q (.node event.declaration.id ds) (event.receipts ++ later)

inductive GeneralForest [judgment : ReplayJudgment] (s : State) : List Request → List Dictionary → List OrderedReceipt → Type where
  | nil : GeneralForest s [] [] []
  | cons :
      GeneralTree s q d now → GeneralForest s qs ds later →
      GeneralForest s (q::qs) (d::ds) (now ++ later)
end

abbrev LiteralSourceTrace (judgment : ReplayJudgment) (s : State) :=
  SourceEventTrace381 (LiteralTraceRule judgment s)

abbrev LiteralSourceForest (judgment : ReplayJudgment) (s : State) :=
  SourceEventForest381 (LiteralTraceRule judgment s)

mutual
/-- Pair the supplied source and lowered derivations using the
same local event value, not equal keys or a reconstructed proof. -/
inductive LiteralReplayPair (judgment : ReplayJudgment) (s : State) :
    {q : Request} → {t : Tree} → {d : Dictionary} → {written : List OrderedReceipt} →
    LiteralSourceTrace judgment s q t → GeneralTree (judgment := judgment) s q d written → Prop where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩)
      {sourceKids : LiteralSourceForest judgment s event.kids ts}
      {loweredKids : GeneralForest (judgment := judgment) s event.kids ds later} :
      LiteralReplayForest judgment s sourceKids loweredKids →
      LiteralReplayPair judgment s (.selected ⟨q,event⟩ guard sourceKids) (.node event guard loweredKids)

inductive LiteralReplayForest (judgment : ReplayJudgment) (s : State) :
    {qs : List Request} → {ts : List Tree} → {ds : List Dictionary} → {written : List OrderedReceipt} →
    LiteralSourceForest judgment s qs ts → GeneralForest (judgment := judgment) s qs ds written → Prop where
  | nil : LiteralReplayForest judgment s .nil .nil
  | cons :
      LiteralReplayPair judgment s sourceHead loweredHead →
      LiteralReplayForest judgment s sourceTail loweredTail →
      LiteralReplayForest judgment s (.cons sourceHead sourceTail) (.cons loweredHead loweredTail)
end

/-- The trace is explicit data. The incoming diagnostic derivation
does not reconstruct its event via proof irrelevance. `input` is
the literal diagnostic index, not an independently chosen tree. -/
structure LiteralTreeFrom [judgment : ReplayJudgment] {s : State} {q : Request}
    {t : Tree} {d : Dictionary} {written : List OrderedReceipt}
    (_tree : Resolves (LocalSource (judgment := judgment) s) q t)
    (input : Tree) (lowered : GeneralTree s q d written) where
  literalInput : input = t
  source : LiteralSourceTrace judgment s q input
  paired : LiteralReplayPair judgment s source lowered

end Yulang.GeneralDeclarativeI65
