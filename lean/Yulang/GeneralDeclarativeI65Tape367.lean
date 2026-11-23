import Yulang.GeneralDeclarativeI65Rivals367
import Yulang.GeneralDeclarativeLowerKnown321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeLowerKnown321 (Tag Knows constructorTag)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)

structure AuthoredCandidate (s : State) (q : Request) (row : Declaration) where
  inScope : row ∈ visible s q
  covered : DeclarationCovered s.current.environment row
  signature : row.Signature (authoredRegistry s.current).roles
  head : SourceHead s q row

/-- A positive reason that an inspection is waiting on unresolved
outputs, not the absence of a checker match or inability to decode a
witness. This reason is for a currently observed ordinary origin. -/
structure PendingCandidate (s : State) (q : Request) (row : Declaration) where
  index : Nat
  arg : Capture
  input : q.demand.arguments[index]? = some arg
  head : Pattern
  source : row.head[index]? = some head
  written : ∃ key params,head = .app key params
  complete : Nat → Prop
  authority : Supported s.current.ordinary complete
  original : Equation
  fromLower : GeneralDeclarativeLowerKnown321.Alias s.current.ordinary arg.lower original.left
  tag : Tag
  structural : constructorTag original.right = some tag
  appears : ∃ owner,authority.derivesFrom original (.output owner) ∧ ¬complete owner
  onlyPending : ∀ o,authority.derivesFrom original o → ∃ owner,o = .output owner ∧ ¬complete owner
  noIndependent : ∀ label,¬Knows (restriction authority) arg.lower label

theorem pending_cannot_be_used_as_input {s : State} {q : Request} {row : Declaration}
    (later : PendingCandidate s q row) :
    later.original ∉ (restriction later.authority).equations ∧
      ∃ arg ∈ q.demand.arguments, ∀ label,¬Knows (restriction later.authority) arg.lower label :=
  ⟨GeneralDeclarativeOrigins321.pending_only later.authority later.original later.onlyPending,
    ⟨later.arg,List.mem_of_getElem? later.input,later.noIndependent⟩⟩

inductive Assessment (s : State) (q : Request) (row : Declaration) : Type where
  | matched : AuthoredCandidate s q row → Assessment s q row
  | incompatible : RigidCandidateMiss s q row → Assessment s q row
  | waiting : PendingCandidate s q row → Assessment s q row

/-- Every visible declaration is retained in the index of a complete
scan. Unsupported certificate shapes produce no such scan, never an
incompatibility entry by default. -/
inductive CandidateTape (s : State) (q : Request) : List Declaration → Type where
  | nil : CandidateTape s q []
  | next : Assessment s q row → CandidateTape s q rest → CandidateTape s q (row::rest)

def CandidateTape.live {s q rows} (t : CandidateTape s q rows) : List Declaration :=
  match t with
  | .nil => []
  | @CandidateTape.next _ _ row _ (.matched _) tail => row :: tail.live
  | .next (.incompatible _) tail | .next (.waiting _) tail => tail.live

def CandidateTape.waits {s q rows} (t : CandidateTape s q rows) : Bool :=
  match t with
  | .nil => false
  | .next (.waiting _) _ => true
  | .next (.matched _) tail | .next (.incompatible _) tail => tail.waits

inductive Stores {s : State} {q : Request} :
    {rows : List Declaration} → CandidateTape s q rows →
      {row : Declaration} → AuthoredCandidate s q row → Prop where
  | here (c : AuthoredCandidate s q row) (rest : CandidateTape s q rows) :
      Stores (.next (.matched c) rest) c
  | later (status : Assessment s q row) {rest : CandidateTape s q rows} :
      Stores rest c → Stores (.next status rest) c

theorem live_readback {s : State} {q : Request} {rows : List Declaration} (t : CandidateTape s q rows)
    (v : Declaration) (seen : v ∈ t.live) :
    ∃ c : AuthoredCandidate s q v, Stores t c := by
  induction t with
  | nil => cases seen
  | @next d ds a bs ih =>
    cases a with
    | matched c =>
      rw [CandidateTape.live] at seen
      rcases List.mem_cons.mp seen with h|tail
      · cases h; exact ⟨c,.here c bs⟩
      · obtain ⟨got,whereAt⟩ := ih tail
        exact ⟨got,.later _ whereAt⟩
    | incompatible h =>
      obtain ⟨got,whereAt⟩ := ih (by simpa [CandidateTape.live] using seen)
      exact ⟨got,.later _ whereAt⟩
    | waiting h =>
      obtain ⟨got,whereAt⟩ := ih (by simpa [CandidateTape.live] using seen)
      exact ⟨got,.later _ whereAt⟩

theorem tape_waiting_origin {s : State} {q : Request} {rows : List Declaration} (t : CandidateTape s q rows) :
    t.waits = true → ∃ row ∈ rows,Nonempty (PendingCandidate s q row) := by
  induction t with
  | nil => simp [CandidateTape.waits]
  | @next d ds a bs ih =>
    cases a with
    | waiting reason => exact fun _ => ⟨d,List.mem_cons_self,⟨reason⟩⟩
    | matched _ =>
      intro wait
      obtain ⟨e,inRows,r⟩ := ih (by simpa [CandidateTape.waits] using wait)
      exact ⟨e,List.mem_cons_of_mem _ inRows,r⟩
    | incompatible _ =>
      intro wait
      obtain ⟨e,inRows,r⟩ := ih (by simpa [CandidateTape.waits] using wait)
      exact ⟨e,List.mem_cons_of_mem _ inRows,r⟩

section
variable {s : State} {q : Request} {rows : List Declaration}

theorem every_nonlive_unblocked_row_is_a_real_miss {t : CandidateTape s q rows}
    (quiet : t.waits = false) {v : Declaration} (present : v ∈ rows) (no : v ∉ t.live) :
    Nonempty (RigidCandidateMiss s q v) := by
  induction t with
  | nil => cases present
  | @next d ds a bs ih =>
    cases a with
    | waiting h => simp [CandidateTape.waits] at quiet
    | matched c =>
      rw [CandidateTape.live] at no
      rcases List.mem_cons.mp present with eq|tail
      · exact False.elim (no (List.mem_cons.mpr (.inl eq)))
      · exact ih (by simpa [CandidateTape.waits] using quiet) tail
          (fun happens => no (List.mem_cons_of_mem _ happens))
    | incompatible m =>
      rcases List.mem_cons.mp present with eq|tail
      · cases eq; exact ⟨m⟩
      · exact ih (by simpa [CandidateTape.waits] using quiet) tail
          (by simpa [CandidateTape.live] using no)

end

end Yulang.GeneralDeclarativeI65
