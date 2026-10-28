import YulangClosure.BirthLevelSCC
import YulangClosure.RecordBoundaryPreservation

/-!
Finite endpoint routing for the unchanged-view graph of the original manuscript,
lines 479–552.  Concrete query success never adds an identity edge.  Every query
retains its whole producer and consumer records, including opaque contextual and
complete-Call payloads.  This is a proof-side finite construction, not a native
checking pass or a proof of authentic edge licensing or source inference.
-/
namespace YulangClosure.BoundaryQueryClosure
open BirthLevelSCC (Reach)

inductive Kind where
  | value | effect
  deriving DecidableEq, Repr

/-- The bound is a finite global port universe, for example from a finite trace. -/
abbrev Port (n : Nat) := Kind × Fin n

/-- Use the constructive finite equality directly; the generic ordered Fin
BEq package carries irrelevant classical order-law dependencies in this pin. -/
local instance portBEq {n : Nat} : BEq (Port n) := ⟨fun a b => decide (a = b)⟩

local instance portLawfulBEq {n : Nat} : LawfulBEq (Port n) where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

def ports (n : Nat) : List (Port n) :=
  [Kind.value, Kind.effect].flatMap fun k => (List.finRange n).map (k, ·)

@[simp] theorem mem_ports {n : Nat} (p : Port n) : p ∈ ports n := by
  rcases p with ⟨k, i⟩
  cases k <;> simp [ports, List.mem_finRange]

abbrev Pair (n : Nat) := Port n × Port n

def pairUniverse (n : Nat) : List (Pair n) :=
  (ports n).flatMap fun a => (ports n).map (a, ·)

@[simp] theorem mem_pairUniverse {n : Nat} (p : Pair n) : p ∈ pairUniverse n := by
  rcases p with ⟨a,b⟩
  simp [pairUniverse]

/-- Supplied wiring still needs its authentic source/context eligibility proof.
The routing algebra independently enforces the kind boundary. -/
def Edge {n : Nat} (wiring : List (Pair n)) (a b : Port n) : Prop :=
  (a,b) ∈ wiring ∧ a.1 = b.1

instance {n : Nat} (wiring : List (Pair n)) (a b : Port n) :
    Decidable (Edge wiring a b) := inferInstanceAs (Decidable (_ ∧ _))

def initial {n : Nat} (wiring : List (Pair n)) : List (Pair n) :=
  (pairUniverse n).filter fun p => p.1 = p.2 ∨ Edge wiring p.1 p.2

@[simp] theorem mem_initial {n : Nat} (wiring : List (Pair n)) (a b : Port n) :
    (a,b) ∈ initial wiring ↔ a = b ∨ Edge wiring a b := by
  simp [initial]

/-- One syntactic route-composition round; no concrete comparison is consulted. -/
def fires {n : Nat} (prior : List (Pair n)) (p : Pair n) : Bool :=
  (ports n).any fun b => decide ((p.1,b) ∈ prior ∧ (b,p.2) ∈ prior)

@[simp] theorem fires_iff {n : Nat} (prior : List (Pair n)) (a c : Port n) :
    fires prior (a,c) = true ↔ ∃ b, (a,b) ∈ prior ∧ (b,c) ∈ prior := by
  simp [fires, List.any_eq_true]

def remaining {n : Nat} (prior pending : List (Pair n)) : List (Pair n) :=
  pending.filter fun p => !fires prior p

def additions {n : Nat} (prior pending : List (Pair n)) : List (Pair n) :=
  pending.filter (fires prior)

def Separate {n : Nat} (prior pending : List (Pair n)) : Prop :=
  ∀ p, p ∈ pending → p ∉ prior

theorem additions_new {n : Nat} {prior pending : List (Pair n)}
    (separate : Separate prior pending) :
    ∀ p, p ∈ additions prior pending → p ∉ prior :=
  fun p hp => separate p (List.mem_filter.mp hp).1

theorem remaining_separate {n : Nat} {prior pending : List (Pair n)}
    (separate : Separate prior pending) :
    Separate (prior ++ additions prior pending) (remaining prior pending) := by
  intro p hp old
  obtain ⟨member, failed⟩ := List.mem_filter.mp hp
  rcases List.mem_append.mp old with old | added
  · exact separate p member old
  · have fired := (List.mem_filter.mp added).2
    simp [fired] at failed

theorem remaining_strict {n : Nat} {prior pending : List (Pair n)}
    (changed : remaining prior pending ≠ pending) :
    (remaining prior pending).length < pending.length := by
  have le := List.length_filter_le (fun p => !fires prior p) pending
  have ne : (remaining prior pending).length ≠ pending.length := by
    intro same
    exact changed (List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp same))
  change (remaining prior pending).length ≤ pending.length at le
  omega

/-- The initial pending cardinality is proved sufficient below, not guessed fuel. -/
def close {n : Nat} : Nat → List (Pair n) → List (Pair n) → List (Pair n)
  | 0, _, prior => prior
  | fuel + 1, pending, prior =>
      let next := remaining prior pending
      if next = pending then prior
      else close fuel next (prior ++ additions prior pending)

def Closed {n : Nat} (prior : List (Pair n)) : Prop :=
  ∀ a b c, (a,b) ∈ prior → (b,c) ∈ prior → (a,c) ∈ prior

theorem close_retains {n : Nat} (fuel : Nat) (pending prior : List (Pair n)) :
    ∀ p, p ∈ prior → p ∈ close fuel pending prior := by
  induction fuel generalizing pending prior with
  | zero => exact fun _ hp => hp
  | succ fuel ih =>
      simp only [close]
      split
      · exact fun _ hp => hp
      · exact fun p hp => ih _ _ p (List.mem_append_left _ hp)

theorem close_closed {n : Nat} (fuel : Nat) (pending prior : List (Pair n))
    (enough : pending.length ≤ fuel)
    (covered : ∀ p, p ∈ pending ∨ p ∈ prior) :
    Closed (close fuel pending prior) := by
  induction fuel generalizing pending prior with
  | zero =>
      have empty : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      exact fun a _ c _ _ => (covered (a,c)).resolve_left (by simp)
  | succ fuel ih =>
      simp only [close]
      split
      · rename_i fixed
        intro a b c hab hbc
        rcases covered (a,c) with member | member
        · have failed := List.filter_eq_self.mp fixed (a,c) member
          have fired := (fires_iff prior a c).mpr ⟨b,hab,hbc⟩
          simp [fired] at failed
        · exact member
      · rename_i changed
        apply ih
        · have strict := remaining_strict changed
          omega
        · intro p
          rcases covered p with old | old
          · by_cases fired : fires prior p = true
            · exact Or.inr (List.mem_append_right _ (List.mem_filter.mpr ⟨old,fired⟩))
            · exact Or.inl (List.mem_filter.mpr ⟨old,by simpa using fired⟩)
          · exact Or.inr (List.mem_append_left _ old)

theorem close_sound {n : Nat} (wiring : List (Pair n)) (fuel : Nat)
    (pending prior : List (Pair n))
    (sound : ∀ p, p ∈ prior → Reach (Edge wiring) p.1 p.2) :
    ∀ p, p ∈ close fuel pending prior → Reach (Edge wiring) p.1 p.2 := by
  induction fuel generalizing pending prior with
  | zero => exact sound
  | succ fuel ih =>
      simp only [close]
      split
      · exact sound
      · apply ih
        intro p hp
        rcases List.mem_append.mp hp with old | added
        · exact sound p old
        · obtain ⟨b,left,right⟩ := (fires_iff prior p.1 p.2).mp (List.mem_filter.mp added).2
          exact (sound _ left).trans (sound _ right)

def pending {n : Nat} (wiring : List (Pair n)) : List (Pair n) :=
  (pairUniverse n).filter fun p => p ∉ initial wiring

theorem pending_separate {n : Nat} (wiring : List (Pair n)) :
    Separate (initial wiring) (pending wiring) :=
  fun _ hp => of_decide_eq_true (List.mem_filter.mp hp).2

def routes {n : Nat} (wiring : List (Pair n)) : List (Pair n) :=
  close (pending wiring).length (pending wiring) (initial wiring)

/-- An execution receipt for the actual closure: every changing round adds
only new memberships and strictly decreases its finite pending list. -/
inductive Runs {n : Nat} : List (Pair n) → List (Pair n) → List (Pair n) → Prop
  | stop {pending prior} (fixed : remaining prior pending = pending) :
      Runs pending prior prior
  | step {pending prior result}
      (fresh : ∀ p, p ∈ additions prior pending → p ∉ prior)
      (decreases : (remaining prior pending).length < pending.length)
      (tail : Runs (remaining prior pending) (prior ++ additions prior pending) result) :
      Runs pending prior result

theorem close_runs {n : Nat} (fuel : Nat) (pending prior : List (Pair n))
    (enough : pending.length ≤ fuel) (separate : Separate prior pending) :
    Runs pending prior (close fuel pending prior) := by
  induction fuel generalizing pending prior with
  | zero =>
      have empty : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      exact Runs.stop rfl
  | succ fuel ih =>
      simp only [close]
      split
      · rename_i fixed
        exact Runs.stop fixed
      · rename_i changed
        have strict := remaining_strict changed
        exact Runs.step (additions_new separate) strict
          (ih _ _ (by omega) (remaining_separate separate))

theorem routes_runs {n : Nat} (wiring : List (Pair n)) :
    Runs (pending wiring) (initial wiring) (routes wiring) :=
  close_runs _ _ _ (Nat.le_refl _) (pending_separate wiring)

theorem routes_closed {n : Nat} (wiring : List (Pair n)) : Closed (routes wiring) := by
  apply close_closed _ _ _ (Nat.le_refl _)
  intro p
  by_cases h : p ∈ initial wiring
  · exact Or.inr h
  · exact Or.inl (List.mem_filter.mpr ⟨mem_pairUniverse p,by simpa using h⟩)

theorem initial_retained {n : Nat} (wiring : List (Pair n)) :
    ∀ p, p ∈ initial wiring → p ∈ routes wiring := close_retains _ _ _

theorem routes_exact {n : Nat} (wiring : List (Pair n)) (a b : Port n) :
    (a,b) ∈ routes wiring ↔ Reach (Edge wiring) a b := by
  constructor
  · apply close_sound
    intro p hp
    rcases (mem_initial wiring p.1 p.2).mp hp with same | edge
    · exact same ▸ Reach.refl
    · exact Reach.cons edge Reach.refl
  · intro path
    induction path with
    | refl => exact initial_retained wiring _ ((mem_initial _ _ _).mpr (Or.inl rfl))
    | cons h _ ih =>
        exact routes_closed wiring _ _ _
          (initial_retained wiring _ ((mem_initial _ _ _).mpr (Or.inr h))) ih

theorem reach_kind {n : Nat} {wiring : List (Pair n)} {a b : Port n}
    (path : Reach (Edge wiring) a b) : a.1 = b.1 := by
  induction path with
  | refl => rfl
  | cons h _ ih => exact h.2.trans ih

theorem reach_empty_iff {n : Nat} (a b : Port n) :
    Reach (Edge []) a b ↔ a = b := by
  constructor
  · intro path
    cases path with
    | refl => rfl
    | cons h _ => cases h.1
  · intro h
    subst b
    exact Reach.refl

structure Anchor (n : Nat) (Head Origin : Type) where
  port : Port n
  head : Head
  origin : Origin
  deriving DecidableEq

/-- Tag may contain full Call/effect evidence. No scalar projection is taken. -/
structure Demand (n : Nat) (Head Boundary Context Occurrence Tag : Type) where
  port : Port n
  target : Head
  boundary : Boundary
  context : Context
  occurrence : Occurrence
  tag : Tag
  deriving DecidableEq

structure Query (n : Nat) (Head Origin Boundary Context Occurrence Tag : Type) where
  producer : Anchor n Head Origin
  consumer : Demand n Head Boundary Context Occurrence Tag
  deriving DecidableEq

structure Input (n : Nat) (Head Origin Boundary Context Occurrence Tag : Type) where
  wiring : List (Pair n)
  anchors : List (Anchor n Head Origin)
  demands : List (Demand n Head Boundary Context Occurrence Tag)
  direct : List (Query n Head Origin Boundary Context Occurrence Tag)

variable {n : Nat} {H O B C X T : Type}
local notation "A" => Anchor n H O
local notation "D" => Demand n H B C X T
local notation "Q" => Query n H O B C X T
local notation "I" => Input n H O B C X T

def routed (i : I) : List Q :=
  i.anchors.flatMap fun a =>
    (i.demands.filter fun d => (a.port,d.port) ∈ routes i.wiring).map (Query.mk a)

def complete (i : I) : List Q := i.direct ++ routed i

def lowerAt (i : I) (v : Port n) : List A :=
  i.anchors.filter fun a => (a.port,v) ∈ routes i.wiring

def upperAt (i : I) (v : Port n) : List D :=
  i.demands.filter fun d => (v,d.port) ∈ routes i.wiring

theorem lowerAt_exact (i : I) (v : Port n) (a : A) :
    a ∈ lowerAt i v ↔ a ∈ i.anchors ∧ Reach (Edge i.wiring) a.port v := by
  simp [lowerAt, routes_exact]

theorem upperAt_exact (i : I) (v : Port n) (d : D) :
    d ∈ upperAt i v ↔ d ∈ i.demands ∧ Reach (Edge i.wiring) v d.port := by
  simp [upperAt, routes_exact]

theorem routed_exact (i : I) (q : Q) :
    q ∈ routed i ↔ q.producer ∈ i.anchors ∧ q.consumer ∈ i.demands ∧
      Reach (Edge i.wiring) q.producer.port q.consumer.port := by
  rcases q with ⟨a,d⟩
  simp [routed, List.mem_flatMap, routes_exact]

theorem query_at_meeting_port (i : I) (q : Q) :
    q ∈ routed i ↔ ∃ v, q.producer ∈ lowerAt i v ∧ q.consumer ∈ upperAt i v := by
  rw [routed_exact]
  constructor
  · rintro ⟨ha,hd,path⟩
    exact ⟨q.consumer.port,(lowerAt_exact _ _ _).mpr ⟨ha,path⟩,
      (upperAt_exact _ _ _).mpr ⟨hd,Reach.refl⟩⟩
  · rintro ⟨v,ha,hd⟩
    obtain ⟨ha,left⟩ := (lowerAt_exact _ _ _).mp ha
    obtain ⟨hd,right⟩ := (upperAt_exact _ _ _).mp hd
    exact ⟨ha,hd,left.trans right⟩

/-- Exact endpoint coverage, with the original records rather than endpoint IDs. -/
theorem complete_exact (i : I) (q : Q) :
    q ∈ complete i ↔ q ∈ i.direct ∨
      (q.producer ∈ i.anchors ∧ q.consumer ∈ i.demands ∧
       Reach (Edge i.wiring) q.producer.port q.consumer.port) := by
  simp [complete, routed_exact]

theorem routed_kind (i : I) (q : Q) (h : q ∈ routed i) :
    q.producer.port.1 = q.consumer.port.1 :=
  reach_kind ((routed_exact i q).mp h).2.2

/-- Direct query successes never become graph edges or additional routed pairs. -/
theorem direct_does_not_change_routes (i : I) (direct : List Q) :
    routed {i with direct := direct} = routed i := rfl

theorem completion_order_independent (i j : I)
    (wiring : ∀ p, p ∈ i.wiring ↔ p ∈ j.wiring)
    (anchors : ∀ a, a ∈ i.anchors ↔ a ∈ j.anchors)
    (demands : ∀ d, d ∈ i.demands ↔ d ∈ j.demands)
    (direct : ∀ q, q ∈ i.direct ↔ q ∈ j.direct) (q : Q) :
    q ∈ complete i ↔ q ∈ complete j := by
  have paths (a b : Port n) : Reach (Edge i.wiring) a b ↔ Reach (Edge j.wiring) a b := by
    constructor
    · exact Reach.mono (fun x y h => ⟨(wiring (x,y)).mp h.1,h.2⟩)
    · exact Reach.mono (fun x y h => ⟨(wiring (x,y)).mpr h.1,h.2⟩)
  simp only [complete_exact, direct, anchors, demands, paths]

/-- Equality retains every identity/payload, even if numeric endpoints coincide. -/
theorem query_eq_iff (a a' : A) (d d' : D) :
    (Query.mk a d : Q) = Query.mk a' d' ↔ a = a' ∧ d = d' := by
  simp

theorem origin_retained (a a' : A) (d d' : D)
    (h : (Query.mk a d : Q) = Query.mk a' d') : a.origin = a'.origin :=
  congrArg Anchor.origin ((query_eq_iff a a' d d').mp h).1

theorem consumer_retained (a a' : A) (d d' : D)
    (h : (Query.mk a d : Q) = Query.mk a' d') :
    d.boundary = d'.boundary ∧ d.context = d'.context ∧
    d.occurrence = d'.occurrence ∧ d.tag = d'.tag := by
  have eq := ((query_eq_iff a a' d d').mp h).2
  cases eq
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Events can include constructor-generated children. Their source authenticity
and a finite containing port universe are external application obligations. -/
inductive Event (n : Nat) (H O B C X T : Type) where
  | edge (a b : Port n)
  | lower (a : Anchor n H O)
  | upper (d : Demand n H B C X T)
  | direct (q : Query n H O B C X T)
  | adaptation (input : Demand n H B C X T) (output : Anchor n H O)
      (distinct : input.port ≠ output.port)

local notation "E" => Event n H O B C X T

def insertEvent (i : I) : E → I
  | .edge a b => {i with wiring := i.wiring ++ [(a,b)]}
  | .lower a => {i with anchors := i.anchors ++ [a]}
  | .upper d => {i with demands := i.demands ++ [d]}
  | .direct q => {i with direct := i.direct ++ [q]}
  | .adaptation d a _ => {i with anchors := i.anchors ++ [a], demands := i.demands ++ [d]}

theorem adaptation_stops_identity (i : I) (d : D) (a : A) (h : d.port ≠ a.port) :
    (insertEvent i (.adaptation d a h)).wiring = i.wiring := rfl

structure Completed (n : Nat) (H O B C X T : Type) where
  input : Input n H O B C X T
  queries : List (Query n H O B C X T)

def finish (i : I) : Completed n H O B C X T := ⟨i,complete i⟩

/-- Re-compute closure after each finite event, including newly created wiring. -/
def advance (s : Completed n H O B C X T) (e : E) : Completed n H O B C X T :=
  finish (insertEvent s.input e)

def run (i : I) (events : List E) : Completed n H O B C X T :=
  events.foldl advance (finish i)

theorem advance_exact (s : Completed n H O B C X T) (e : E) (q : Q) :
    q ∈ (advance s e).queries ↔ q ∈ (advance s e).input.direct ∨
      (q.producer ∈ (advance s e).input.anchors ∧
       q.consumer ∈ (advance s e).input.demands ∧
       Reach (Edge (advance s e).input.wiring) q.producer.port q.consumer.port) :=
  complete_exact _ _

theorem run_completed (i : I) (events : List E) :
    (run i events).queries = complete (run i events).input := by
  suffices ∀ s : Completed n H O B C X T,
      s.queries = complete s.input →
      (events.foldl advance s).queries = complete (events.foldl advance s).input from
    this (finish i) rfl
  induction events with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun s _ => ih (advance s e) rfl

/-- Applies separately at every finite prefix; no fixed-graph theorem is applied
to an evolving graph, and no termination of an arbitrary event generator is asserted. -/
theorem run_exact (i : I) (events : List E) (q : Q) :
    q ∈ (run i events).queries ↔ q ∈ (run i events).input.direct ∨
      (q.producer ∈ (run i events).input.anchors ∧
       q.consumer ∈ (run i events).input.demands ∧
       Reach (Edge (run i events).input.wiring) q.producer.port q.consumer.port) := by
  rw [run_completed]
  exact complete_exact _ _

namespace Witness
open RecordBoundary

abbrev Head := List (Field RecordBoundary.Witness.Atom)
abbrev WAnchor := Anchor 3 Head Nat
abbrev WDemand := Demand 3 Head Nat Nat Nat Nat
abbrev WQuery := Query 3 Head Nat Nat Nat Nat Nat
abbrev WInput := Input 3 Head Nat Nat Nat Nat Nat

def p0 : Port 3 := (.value,0)
def p1 : Port 3 := (.value,1)
def p2 : Port 3 := (.value,2)
def a : WAnchor := ⟨p0,RecordBoundary.Witness.a,10⟩
def b : WAnchor := ⟨p1,RecordBoundary.Witness.b,11⟩
def c : WAnchor := ⟨p2,RecordBoundary.Witness.c,12⟩
def wantB : WDemand := ⟨p0,RecordBoundary.Witness.b,20,30,40,50⟩
def wantC : WDemand := ⟨p1,RecordBoundary.Witness.c,21,31,41,51⟩
def ac : WQuery := ⟨a,wantC⟩
def unchanged : WInput := ⟨[(p0,p1)],[a],[wantC],[]⟩
def base : WInput := ⟨[],[a],[],[]⟩
def adaptations : List (Event 3 Head Nat Nat Nat Nat Nat) :=
  [.adaptation wantB b (by decide), .adaptation wantC c (by decide)]

/-- The original optional-string/optional-int query is emitted across identity
wiring, and the already-proved record compiler rejects that direct comparison. -/
theorem unchanged_emits_failing_direct_query :
    ac ∈ complete unchanged ∧
    compile (signature RecordBoundary.Witness.a) RecordBoundary.Witness.noPresence
      RecordBoundary.Witness.resolve RecordBoundary.Witness.c = none := by
  constructor
  · apply (complete_exact unchanged ac).mpr
    exact Or.inr ⟨by decide,by decide,Reach.cons (by decide) Reach.refl⟩
  · exact RecordBoundary.Witness.direct_comparison_nontransitive.2.2

theorem adaptation_ports_distinct : wantB.port ≠ b.port ∧ wantC.port ≠ c.port := by
  decide

theorem adaptation_wiring_empty : (run base adaptations).input.wiring = [] := rfl

/-- Two actual adaptation events through the empty B retain A→B and B→C
queries, but create no A→C identity route or corresponding query. -/
theorem two_adaptations_do_not_emit_ac :
    (Query.mk a wantB : WQuery) ∈ (run base adaptations).queries ∧
    (Query.mk b wantC : WQuery) ∈ (run base adaptations).queries ∧
    ac ∉ (run base adaptations).queries := by
  constructor
  · apply (run_exact base adaptations _).mpr
    exact Or.inr ⟨by decide,by decide,Reach.refl⟩
  constructor
  · apply (run_exact base adaptations _).mpr
    exact Or.inr ⟨by decide,by decide,Reach.refl⟩
  · intro h
    rcases (run_exact base adaptations ac).mp h with direct | routed
    · exact (by decide : ac ∉ (run base adaptations).input.direct) direct
    · have same := (reach_empty_iff a.port wantC.port).mp routed.2.2
      exact (by decide : a.port ≠ wantC.port) same

/-- Equal endpoint numbers do not collapse distinct provenance records. -/
theorem coincident_endpoints_retain_identities :
    (Query.mk a wantC : WQuery) ≠ Query.mk {a with origin := 99} wantC ∧
    (Query.mk a wantC : WQuery) ≠ Query.mk a {wantC with boundary := 99} ∧
    (Query.mk a wantC : WQuery) ≠ Query.mk a {wantC with context := 99} ∧
    (Query.mk a wantC : WQuery) ≠ Query.mk a {wantC with occurrence := 99} ∧
    (Query.mk a wantC : WQuery) ≠ Query.mk a {wantC with tag := 99} := by
  simp [a,wantC]

theorem late_edge_enables_old_endpoint_query :
    ac ∉ complete {unchanged with wiring := []} ∧
    ac ∈ (run {unchanged with wiring := []} [.edge p0 p1]).queries := by
  constructor
  · intro h
    rcases (complete_exact _ ac).mp h with direct | routed
    · cases direct
    · have same := (reach_empty_iff a.port wantC.port).mp routed.2.2
      exact (by decide : a.port ≠ wantC.port) same
  · apply (run_exact _ _ _).mpr
    exact Or.inr ⟨by decide,by decide,Reach.cons (by decide) Reach.refl⟩

end Witness

end YulangClosure.BoundaryQueryClosure
