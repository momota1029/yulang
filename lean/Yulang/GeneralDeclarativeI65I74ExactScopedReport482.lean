import Yulang.GeneralDeclarativeI65I74NamedTerminalRoute482
import Yulang.GeneralDeclarativeI65I74TypedCompletedFocus482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open InputCoordinates475 (QueryStep476 SamePhaseInputObservation478)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open Producer479 (PriorPhase)
open NativeProducer465 (CheckedPhase)
open ObservationAlternatives473 (Positions)

/-- Legacy path discriminants are compared as data only. This does not
license an extra join visit in any supplied route. -/
def queryStepMatches : QueryStep476 → QueryStep476 → Bool
  | .field a, .field b => a == b
  | .argument a, .argument b => a == b
  | .variantPayload,.variantPayload | .legacyJoinLeft,.legacyJoinLeft
  | .legacyJoinRight,.legacyJoinRight => true
  | _,_ => false

theorem query_step_matches_exactly (a b : QueryStep476) :
    queryStepMatches a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [queryStepMatches]

def queryPathMatches : List QueryStep476 → List QueryStep476 → Bool
  | [],[] => true
  | a::later,b::rest => queryStepMatches a b && queryPathMatches later rest
  | _,_ => false

theorem query_path_matches_exactly (a b : List QueryStep476) :
    queryPathMatches a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [queryPathMatches]
  | cons step rest ih =>
    cases b <;> simp [queryPathMatches,query_step_matches_exactly,ih]

def signedReportMatches (expected actual : SamePhaseInputObservation478) : Bool :=
  decide (expected.frame = actual.frame ∧ expected.rootArgument = actual.rootArgument ∧
    expected.outcome.1 = actual.outcome.1 ∧ expected.outcome.2.2.1 = actual.outcome.2.2.1 ∧
    expected.outcome.2.2.2 = actual.outcome.2.2.2) &&
  queryPathMatches expected.outcome.2.1 actual.outcome.2.1

theorem signed_report_matches_exactly (expected actual : SamePhaseInputObservation478) :
    signedReportMatches expected actual = true ↔ expected = actual := by
  rcases expected with ⟨frame,arg,a,b,c,d⟩
  rcases actual with ⟨otherFrame,otherArg,e,f,g,h⟩
  simp [signedReportMatches,query_path_matches_exactly,SamePhaseInputObservation478.mk.injEq,
    and_left_comm,and_comm,and_assoc]

def checkSignedRead {Receipt : Type} (got : Option Receipt)
    (project : Receipt → SamePhaseInputObservation478) (expected : SamePhaseInputObservation478) : Bool :=
  match got with
  | none => false
  | some found => signedReportMatches expected (project found)

theorem exact_checked_read_cannot_substitute_observation_or_source
    {Receipt : Type} (got : Option Receipt)
    (project : Receipt → SamePhaseInputObservation478) (expected : SamePhaseInputObservation478) :
    checkSignedRead got project expected = true ↔
      ∃ r : Receipt, got = some r ∧ project r = expected := by
  cases got with
  | none => simp [checkSignedRead]
  | some r =>
    simp only [checkSignedRead,signed_report_matches_exactly]
    constructor
    · intro h; exact ⟨r,rfl,h.symm⟩
    · rintro ⟨other,h,eq⟩
      obtain rfl := Option.some.inj h
      exact eq.symm

/-- A scoped comparison against a requested report. This is not a tag
in the adopted legacy flat dispatcher. -/
def checkScopedNamedTerminal482 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (w : NamedTerminalWire n)
    (expected : SamePhaseInputObservation478) : Bool :=
  checkSignedRead (readNamedTerminalRoute p gd pos rel basis w) (·.initial.output) expected

def checkScopedCompleted482 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (basis : PriorPhase) (phase : CheckedPhase p.old.state.core) (w : CompletedFocusWire n)
    (expected : SamePhaseInputObservation478) : Bool :=
  checkSignedRead (readCompletedFocus p gd pos rel basis phase w) (·.output) expected

theorem checked_named_terminal_has_the_literal_scoped_receipt482
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {w : NamedTerminalWire n}
    {expected : SamePhaseInputObservation478} :
    checkScopedNamedTerminal482 p gd pos rel basis w expected = true ↔
    ∃ actual, readNamedTerminalRoute p gd pos rel basis w = some actual ∧ actual.initial.output = expected :=
  exact_checked_read_cannot_substitute_observation_or_source ..

theorem checked_completed_report_has_the_literal_scoped_receipt482
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {w : CompletedFocusWire n} {expected : SamePhaseInputObservation478} :
    checkScopedCompleted482 p gd pos rel basis phase w expected = true ↔
    ∃ actual, readCompletedFocus p gd pos rel basis phase w = some actual ∧ actual.output = expected :=
  exact_checked_read_cannot_substitute_observation_or_source ..

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
