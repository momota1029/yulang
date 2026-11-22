import Yulang.GeneralDeclarativeWitnessTagMix351
import Yulang.GeneralDeclarativeWitnessAuthNode351
import Yulang.GeneralDeclarativeWitnessRank350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagElection352
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeWitnessTagSources351 (Named NamedBounds Script Ref namedBounds directBounds)
open GeneralDeclarativeWitnessTagLocal351 (PatternData Route parse)
open GeneralDeclarativeWitnessBound349 (Range)
open GeneralDeclarativeWitnessTagMix351 (lowerDirect upperDirect)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativePriority321 (Candidates Visible Blocked Survives Recurs)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessOneRecord350 (pointPortal)
open GeneralDeclarativeWitnessPointInput349 (pick picked)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarations (Registry Declaration)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

/-- The input witness describes the actual route taken at each endpoint.
The verifier still derives roles, pattern, coordinates, and readiness
from the anchored problem and source, never from a choice bit. -/
inductive Ends where
  | literal (low high : Ref)
  | recursive (low high : Script)
  | lowerLiteral (low : Ref) (high : Script)
  | upperLiteral (low : Script) (high : Ref)

def reads {s : State} {t : Table} (owner : Attached s t) (arg : Capture) (tag : Nat)
    (span : Range) : Ends → Option (Route owner arg tag)
  | .literal lo hi => (directBounds owner arg tag span lo hi).map .direct
  | .recursive lo hi => (namedBounds owner arg tag span lo hi).map .named
  | .lowerLiteral lo hi => (lowerDirect owner arg tag span lo hi).map .named
  | .upperLiteral lo hi => (upperDirect owner arg tag span lo hi).map .named

def LowerReady {s : State} {t : Table} (src : Attached s t) (arg : Capture) : Prop :=
  ∃ (tag : Nat) (payload : Expr),
    GeneralDeclarativeTaggedNamed340.Source
      (GeneralDeclarativeOrigins321.restriction (support src)) tag (.variable arg.lower) payload

theorem read_is_ready {s : State} {t : Table} {src : Attached s t}
    (read : Route src arg tag) : LowerReady src arg := by
  cases read with
  | direct lo => exact ⟨_,lo.lower,GeneralDeclarativeTaggedNamed340.prior lo.fact.lower⟩
  | named lo => exact ⟨_,lo.lower.payload,lo.lower.actual⟩

def Head {s : State} {t : Table} (src : Attached s t) (r : Registry) (i : Interpretation)
    (arg : Capture) (pat : Pattern) : Prop :=
  ∃ tag, Nonempty (Route src arg tag × PatternData r.constructors i pat tag)

def tests {s : State} {t : Table} (src : Attached s t) (r : Registry) (i : Interpretation) : Candidates :=
  let matched := fun (d : Demand) (impl : Declaration) => All₂ (Head src r i) d.arguments impl.head
  ⟨matched,fun d impl => ¬matched d impl⟩

/-- A sufficient, deliberately narrow independent election: both
endorsed ends, real pattern, one visible candidate, no K2. This says
nothing about the language outcome when a certificate is missing. -/
structure Elected {s : State} {t : Table} (src : Attached s t) (r : Registry)
    (i : Interpretation) (d : Demand) (impl : Declaration) : Prop where
  ready : ∀ arg ∈ d.arguments, LowerReady src arg
  safe : ¬Recurs s r i (tests src r i) d
  clear : ¬Blocked r (tests src r i) d
  choice : Survives r (tests src r i) d impl
  unique : ∀ other, Survives r (tests src r i) d other → other.id = impl.id

theorem elect {s : State} {t : Table} (src : Attached s t)
    {p : Problem} {table : SourceBundle} {impl : Declaration} {arg : Capture} {pat : Pattern}
    (args : p.demand.arguments = [arg]) (pattern : impl.head = [pat])
    (sole : pick (pointPortal p) table = some impl)
    {tag : Nat} (read : Route src arg tag)
    (formed : PatternData (registry table).constructors (interpretation table.snapshot) pat tag)
    {levels : List Nat} (rank : GeneralDeclarativeWitnessRank350.check s levels = true) :
    Elected src (registry table) (interpretation table.snapshot) p.demand impl := by
  obtain ⟨visible,role,only⟩ := picked sole
  have yes : All₂ (Head src (registry table) (interpretation table.snapshot)) p.demand.arguments impl.head := by
    rw [args,pattern]
    exact .cons ⟨tag,⟨read,formed⟩⟩ .nil
  constructor
  · intro here inScope
    have same : here = arg := List.mem_singleton.mp (args ▸ inScope)
    cases same
    exact read_is_ready read
  · exact GeneralDeclarativeWitnessRank350.safe rank
  · rintro ⟨other,h,incomplete⟩
    cases only other h.1 h.2
    exact incomplete yes
  · exact ⟨⟨visible,role⟩,yes⟩
  · intro other h
    cases only other h.1.1 h.1.2
    rfl

end Yulang.GeneralDeclarativeWitnessTagElection352
