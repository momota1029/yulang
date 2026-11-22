import Yulang.GeneralDeclarativeTaggedInputs340
import Yulang.GeneralDeclarativeGraphFootprint326
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedElection340
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTaggedSources340 (Read BoundsRead)
open GeneralDeclarativePriority321 (Candidates Recurs Blocked Survives)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Knows Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeTraceNames321 (names)
open GeneralCandidateInspection (plainNames)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open CommonRoleOutermostResolver (All₂)

structure Match {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (a : Capture) (pat : Pattern) : Prop where
  reads : ∃ tag low high payload seen code, BoundsRead p a tag low high ∧
    normalize pat = .variant tag payload ∧ plainNames payload = some seen ∧
    translate c i payload = some code

inductive Head {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation) :
    Capture → Pattern → Prop where
  | old : GeneralDeclarativeInlineEndpoint331.Matches (restriction p) c i a pat → Head p c i a pat
  | named : GeneralDeclarativeEndpointProbe321.Matches (restriction p) c i a pat → Head p c i a pat
  | merged : Match p c i a pat → Head p c i a pat

def tests {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Candidates :=
  ⟨fun d impl => All₂ (Head p r.constructors i) d.arguments impl.head,waiting⟩

def Ready {s : State} (p : Supported s done) (d : Demand) : Prop :=
  ∀ a ∈ d.arguments,
    (∃ tag, Knows (restriction p) a.lower tag) ∨ (∃ tag payload, Read p a.lower tag payload)

/-- Optional certificate for the positive fragment. Every alias and
all variable occurrences of stored compound rows are checked, including
under joins/calculated payloads. Failure of a certificate is not K2. -/
structure Ranked (s : State) (rank : Nat → Nat) : Prop where
  bounded : ∀ {a b}, Bound s.normal a b → rank a ≤ rank b
  flat : ∀ {a b}, (⟨a,.variable b⟩ : Equation) ∈ s.equations → rank a = rank b
  compound : ∀ row ∈ s.equations, ∀ n ∈ names row.right,
    (∀ b, row.right ≠ .variable b) → rank n < rank row.left

theorem level {s : State} {rank : Nat → Nat} (given : Ranked s rank) (a : Alias s x y) : rank x = rank y := by
  induction a with
  | bounds lo hi => exact Nat.le_antisymm (given.bounded lo) (given.bounded hi)
  | forward eq => exact given.flat eq
  | backward eq => exact (given.flat eq).symm
  | trans _ _ l r => exact l.trans r

theorem no_cycles {s : State} {rank : Nat → Nat} (given : Ranked s rank) :
    ∀ root, ¬AliasCycle s (observed s) root := by
  apply GeneralDeclarativeRank321.graph_no_cycle rank (fun _ _ => level given)
  rintro a shape z ⟨expr,row,known⟩ present
  have linked := GeneralDeclarativeGraphFootprint326.shape_children known present
  refine given.compound ⟨a,expr⟩ row z linked ?_
  intro b named
  change expr = .variable b at named
  subst expr
  cases known

theorem safe {s : State} {rank : Nat → Nat} (given : Ranked s rank) :
    ¬ Recurs s r i t d := by
  rintro (⟨a,_,cycle⟩|⟨_,_,_,a,_,_,_,_,_,here,_,cycle⟩)
  · exact no_cycles given a.lower cycle
  · exact no_cycles given here cycle

/-- Pure positive selection. Keep the existing uniqueness, blocker
and K2 tests and insist on a source guard that inspects compound
operands. No old positive verdict is treated as readiness. -/
structure Election {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) (d : Demand) (impl : Declaration) : Prop where
  ready : Ready p d
  certified : ∃ rank, Ranked s rank
  clear : ¬ Blocked r (tests p r i waiting) d
  viable : Survives r (tests p r i waiting) d impl
  unique : ∀ other, Survives r (tests p r i waiting) d other → other.id = impl.id

theorem guarded {s : State} {p : Supported s done} (positive : Election p r i waiting d impl) :
    ¬ Recurs s r i (tests p r i waiting) d := by
  obtain ⟨_,ranked⟩ := positive.certified
  exact safe ranked

end Yulang.GeneralDeclarativeTaggedElection340
