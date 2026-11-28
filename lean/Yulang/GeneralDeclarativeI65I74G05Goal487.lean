import Yulang.GeneralDeclarativeI65I74IndependentScopedPriority487
import Yulang.GeneralDeclarativeI65I74FlatSound481

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe)
open GeneralDeclarations (Declaration)

inductive G05LocalVerdict487 where
  | rigidMatch | rigidMismatch | unresolved
  deriving DecidableEq

inductive G05CandidateMark487 where
  | requiredCycle
  | nonrecursive (verdict : G05LocalVerdict487)
  deriving DecidableEq

structure G05CandidateRow487 (n : Nat) where
  ordinal : Nat
  observed : List (CandidateVisitKey485 n)
  mark : G05CandidateMark487

inductive G05Priority487 where
  | recursive (actualOriginalOrdinals : List Nat)
  | eligible (rows : List (Nat × G05LocalVerdict487))
  deriving DecidableEq

structure G05Report487 (n : Nat) where
  rows : List (G05CandidateRow487 n)
  priority : G05Priority487

structure G05FiniteWitness487 (n : Nat) where
  roots : List (Checkpoint n)
  tape : List (Nat × PlannedCandidateWire485 n)
  localTokens : List (Option (List Nat))

abbrev G05LocalMeaning487 := Nat → Nat → Declaration → G05LocalVerdict487 → Prop
abbrev G05LocalEvidence487 := Model → Nat → Nat → Declaration → G05LocalVerdict487 → Prop
abbrev G05LocalChecker487 := Nat → Nat → Declaration → List Nat → Option G05LocalVerdict487

def G05PriorityOfRows487 {n : Nat} (rows : List (G05CandidateRow487 n)) : G05Priority487 :=
  let positives := rows.filterMap fun row => match row.mark with
    | .requiredCycle => some row.ordinal
    | .nonrecursive _ => none
  match positives with
  | [] => .eligible (rows.filterMap fun row => match row.mark with
      | .requiredCycle => none
      | .nonrecursive verdict => some (row.ordinal,verdict))
  | first::tail => .recursive (first::tail)

/-- This independence premise concerns the existing local source rule.
A body callback cannot turn an unimplemented check into a mismatch. -/
def G05ExactLocalProtocol487 (check : G05LocalChecker487) (meaning : G05LocalMeaning487) : Prop :=
  (∀ i ord d w v, check i ord d w = some v → meaning i ord d v) ∧
  (∀ i ord d v, meaning i ord d v → ∃ w, check i ord d w = some v)

def G05ExactVisitInputs487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (Allowed : Nat → CandidateVisitKey485 n → Prop) : Prop :=
  (∀ ord key, permit ord key = true ↔ Allowed ord key) ∧
  OriginalRosterPermissionIsPrefixCoherent487 p gd pos rel
    (computedOriginalPalette486 p.old.state.core pos rel) permit ∧
  AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords ∧
  (∀ site ∈ coords, GuardedObservationInput p.old.state.core pos rel site) ∧
  (∀ i : Fin (visible485 p).length, ∀ argument root, coords[argument]? = some root →
    Nonempty (OriginalArgumentStart486 p gd pos i.val argument root))

def G05OriginalVisitsExact487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n)) (i : Nat)
    (Allowed : CandidateVisitKey485 n → Prop) (keys : List (CandidateVisitKey485 n)) : Prop :=
  ∀ key, key ∈ keys ↔ ∃ argument root, (root,argument) ∈ coords.zipIdx ∧
    ∃ head : OriginalArgumentStart486 p gd pos i argument root,
      IndependentScopedVisit487 rel argument head.site Allowed key

def G05ExactCandidateReport487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (r : G05Report487 n) : Prop :=
  r.priority = G05PriorityOfRows487 r.rows ∧ r.rows.length = (visible485 p).length ∧
  ∀ i : Fin (visible485 p).length, ∃ row d,
    r.rows[i.val]? = some row ∧ OriginalRosterCell485 p i.val (row.ordinal,d) ∧
    G05OriginalVisitsExact487 p gd pos rel coords i.val (Allowed row.ordinal) row.observed ∧
    match row.mark with
    | .requiredCycle => IndependentScopedReturn487 p gd pos rel coords Allowed i.val
    | .nonrecursive v =>
      ¬IndependentScopedReturn487 p gd pos rel coords Allowed i.val ∧ meaning i.val row.ordinal d v

def G05HasOriginalModelEvidence487 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (evidence : G05LocalEvidence487) (r : G05Report487 n) : Prop :=
  ∀ m : Model, FitsFull p.state m →
    ∀ (i : Fin (visible485 p).length) (row : G05CandidateRow487 n) (d : Declaration),
      r.rows[i.val]? = some row → OriginalRosterCell485 p i.val (row.ordinal,d) →
      match row.mark with
      | .requiredCycle => IndependentScopedReturn487 p gd pos rel coords Allowed i.val
      | .nonrecursive v => evidence m i.val row.ordinal d v

/-- I-100 target, not a theorem. The full ordered candidate tape keeps
genuine K2, rigid match, definitive mismatch and unresolved distinct.
The local source protocol is a named premise, not derived by this goal. -/
def G05Goal : Prop :=
  ∀ (p : FullProblem) (gd : CheckedTable p.old.state.core.current),
  ∃ check : (n : Nat) → Positions n → List (Fin n × Fin n) → List (Fin n) →
      (Nat → CandidateVisitKey485 n → Bool) → G05LocalChecker487 →
      Sum Flat481.FlatReport (G05Report487 n) →
      Sum Flat481.FlatWitness (G05FiniteWitness487 n) → Bool,
    (∀ n pos rel coords permit localCheck r w,
      check n pos rel coords permit localCheck (.inl r) (.inl w) = Flat481.check_full_flat p r w) ∧
    (∀ n pos rel coords permit localCheck old updated oldWire updateWire,
      check n pos rel coords permit localCheck (.inl old) (.inr updateWire) = false ∧
      check n pos rel coords permit localCheck (.inr updated) (.inl oldWire) = false) ∧
    ∀ n pos rel coords permit localCheck (Allowed : Nat → CandidateVisitKey485 n → Prop)
        (meaning : G05LocalMeaning487) (evidence : G05LocalEvidence487),
      G05ExactVisitInputs487 p gd pos rel coords permit Allowed →
      G05ExactLocalProtocol487 localCheck meaning →
      (∀ m : Model, FitsFull p.state m → ∀ i ord d v, meaning i ord d v → evidence m i ord d v) →
      (∀ r w, check n pos rel coords permit localCheck (.inr r) (.inr w) = true →
        w.roots.map Checkpoint.which = coords ∧ G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
        G05HasOriginalModelEvidence487 p gd pos rel coords Allowed evidence r) ∧
      (∀ r, G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r →
        ∃ w : G05FiniteWitness487 n, w.roots.map Checkpoint.which = coords ∧
          check n pos rel coords permit localCheck (.inr r) (.inr w) = true)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
