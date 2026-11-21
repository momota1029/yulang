import Yulang.GeneralDeclarativeStableSelect329
import Yulang.GeneralDeclarativeStableCanonical329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableAttempt329
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativePriority321 (Candidates Survives Blocked Recurs Local)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableCanonical329 (Representative EqualUses exact)
open GeneralDeclarativeStableTies329 (rows pairOf)
open GeneralDeclarativeStableSelect329 (TieClash)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralNominalInspection (Interpretation)

/-- This is the existing independent provisional election before any
center equation is added. In particular it cannot consult an actual
witness model or use a manufactured shared center as evidence. -/
structure Elected (s : State) (r : Registry) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) (d : Demand)
    (impl : Declaration) : Prop where
  ready : Ready p d
  guarded : ¬Recurs s r i tests d
  clear : ¬Blocked r tests d
  viable : Survives r tests d impl
  unique : ∀ other, Survives r tests d other → other.id = impl.id

structure Attempt (s : State) (r : Registry) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) (d : Demand)
    (impl : Declaration) where
  chosen : Elected s r i p tests d impl
  spans : List (Nat × Capture)
  center : Nat → Capture
  sources : Heads s r.constructors i d.arguments impl.head spans
  actual : Representative center spans

def Attempt.after (tryIt : Attempt s r i p tests d impl) : State :=
  appendFacts s (rows tryIt.center (tryIt.spans.map pairOf))

def Attempt.Clashes (tryIt : Attempt s r i p tests d impl) : Prop :=
  (∃ m, Models s m) ∧ ¬∃ m, Models tryIt.after m

theorem after_exact (tryIt : Attempt s r i p tests d impl) (m) :
    Models tryIt.after m ↔ Models s m ∧ EqualUses m tryIt.spans :=
  exact s tryIt.center tryIt.spans tryIt.actual m

theorem independent_election {s : State} {p : Supported s done}
    (chosen : Elected s r i p tests d impl) (generation : emit d impl kids) :
    Local s r i p tests emit d (.selected impl.id kids) :=
  .selected chosen.ready chosen.guarded chosen.clear chosen.viable chosen.unique generation

/-- Two-stage, relational use only: a proved contradiction *after*
the actual writes is a rejected selected attempt. This does not
decide existence of an election, classify arbitrary diagnostics,
or claim a priority when K2/unsupported already overlap. -/
def RejectedByWrite (tryIt : Attempt s r i p tests d impl) : Prop := tryIt.Clashes

theorem reject_exact (tryIt : Attempt s r i p tests d impl) :
    RejectedByWrite tryIt ↔
      (∃ m, Models s m) ∧ ∀ m, Models s m → ¬EqualUses m tryIt.spans := by
  constructor
  · rintro ⟨inhabited,impossible⟩
    exact ⟨inhabited,fun m old tied => impossible ⟨m,(after_exact tryIt m).mpr ⟨old,tied⟩⟩⟩
  · rintro ⟨inhabited,mismatch⟩
    refine ⟨inhabited,?_⟩
    rintro ⟨m,good⟩
    obtain ⟨old,tied⟩ := (after_exact tryIt m).mp good
    exact mismatch m old tied

theorem no_success (tryIt : Attempt s r i p tests d impl)
    (bad : RejectedByWrite tryIt) {t : State} (stable : Extends tryIt.after t) :
    ¬∃ m, Models t m := by
  rintro ⟨m,good⟩
  exact bad.2 ⟨m,restrict stable m good⟩

theorem stable_writes {s t : State} {p : Supported s done} (tryIt : Attempt s r i p tests d impl)
    (keeps : Extends tryIt.after t) :
    GeneralDeclarativeStableTies329.Consequence t tryIt.center (tryIt.spans.map pairOf) :=
  GeneralDeclarativeStableTies329.present_entails (fun _ h => keeps.equations (List.mem_append_right _ h))

end Yulang.GeneralDeclarativeStableAttempt329
