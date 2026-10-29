import YulangClosure.FormalPermissionStructuralBufferBound

/-! R19, conditional transcription of the selected ordinary call priorCalls.
Source: candidate_source.rs:1280–1340,2354–2488; candidate_effect.rs:1617–1659,
1877–1926; candidate_scheme.rs:2898–2950; lib.rs:3503–3558,9267–9545;
term.rs:713–714,746–822. The two journals are different owners.

`CompletedCall` is a source trace alphabet, NOT an assertion that every native
call is represented. Authentication of the entire graph-plan priorCalls, including
previous members/provider calls, remains open. No caller-state equation is a
hypothesis. Initial state, wrapper microsteps and the selected suffix compute
both active journals. Spare journals are not active journals.
No native execution, allocation observation, or parent closure is claimed. -/
namespace YulangClosure.FormalPermissionCandidateCallJournal
open FormalPermissionStructuralBufferBound

structure Journals where
  session : Option Unit
  arena : Option Unit
  deriving DecidableEq

def initial : Journals := ⟨none, none⟩

/-- Presence projection only; payload restoration/accounting is outside scope.
The Store begins the arena BEFORE the session publishes its journal. -/
inductive Microstep where
  | beginArena | publishSession | takeSession | takeArena | unchanged
  deriving DecidableEq

def step (s : Journals) : Microstep → Journals
  | .beginArena => { s with arena := some () }
  | .publishSession => { s with session := some () }
  | .takeSession => { s with session := none }
  | .takeArena => { s with arena := none }
  | .unchanged => s

def run (s : Journals) (steps : List Microstep) : Journals :=
  steps.foldl step s

/-- Successful wrapper: Store begin; session publication; synchronous body;
session take; Store/arena commit. Body writer coverage remains a source seam. -/
def committedRoute : List Microstep :=
  [.beginArena, .publishSession, .unchanged, .takeSession, .takeArena]

/-- Error finish takes the session and rolls back Store/arena before returning.
The owner calls these transitions also when later accounting reports failure. -/
def rolledBackRoute : List Microstep :=
  [.beginArena, .publishSession, .unchanged, .takeSession, .takeArena]

/-- Preparation can fail after Store begin but before session publication. -/
def failedPreparation : List Microstep := [.beginArena, .takeArena]

theorem committed_route_clears (s : Journals) :
    run s committedRoute = initial := by
  simp [run, committedRoute, step, initial]

theorem rolled_back_route_clears (s : Journals) :
    run s rolledBackRoute = initial := by
  simp [run, rolledBackRoute, step, initial]

theorem failed_preparation_clears :
    run initial failedPreparation = initial := by
  rfl

/-- Named boundaries of the selected direct route; all are synchronous.
This alphabet cannot encode an unreturned transaction body. -/
inductive NeutralCall where
  | startCandidateGraph | execute | sccDispatch | graphPlanSetup
  | sourceRoot | beginSource | driveSource | stepSource
  | beginLambda | formalAnnotationPreparation | tupleScratch | collectedScalar
  deriving DecidableEq

inductive CompletedCall where
  | neutral : NeutralCall → CompletedCall
  | committedRoute : CompletedCall
  deriving DecidableEq

def callSteps : CompletedCall → List Microstep
  | .neutral _ => [.unchanged]
  | .committedRoute => committedRoute

def runCalls : Journals → List CompletedCall → Journals
  | s, [] => s
  | s, c :: cs => runCalls (run s (callSteps c)) cs

/-- Every represented priorCalls starts at actual initialization, rather than an
assumed absent caller frame. Source-to-alphabet correspondence is NOT supplied. -/
theorem completed_prefix_clears (calls : List CompletedCall) :
    runCalls initial calls = initial := by
  induction calls with
  | nil => rfl
  | cons c cs ih =>
      cases c with
      | neutral n => simpa [runCalls, callSteps, run, step] using ih
      | committedRoute => simpa only [runCalls, callSteps, committed_route_clears] using ih

inductive Scalar where
  | bool | str | int | unit
  deriving DecidableEq

/-- The selected priorCalls may have completed calls before the selected root.
No record/unit parameter action or FormalEntry occurs in this scalar-tuple
annotation branch with absent top-level effects. Scalar children allocate no
live terms before the positive tuple call. -/
def selectedSuffix (children : List Scalar) : List CompletedCall :=
  [.neutral .sourceRoot, .neutral .beginSource, .neutral .driveSource,
   .neutral .stepSource, .neutral .beginLambda,
   .neutral .formalAnnotationPreparation, .neutral .tupleScratch] ++
  children.map (fun _ => .neutral .collectedScalar)

def startup : List CompletedCall :=
  [.neutral .startCandidateGraph, .neutral .execute,
   .neutral .sccDispatch, .neutral .graphPlanSetup]

/-- State immediately before positive_tuple/intern_structure; no wrapper has
been entered by with_term_events. No target call success is presumed. -/
def atPositiveTuple (priorCalls : List CompletedCall) (children : List Scalar) : Journals :=
  runCalls initial (startup ++ priorCalls ++ selectedSuffix children)

theorem selected_call_journals (priorCalls : List CompletedCall) (children : List Scalar) :
    atPositiveTuple priorCalls children = initial := by
  exact completed_prefix_clears _

theorem selected_call_arena_absent (priorCalls : List CompletedCall) (children : List Scalar) :
    (atPositiveTuple priorCalls children).arena = none := by
  rw [selected_call_journals]
  rfl

/-- R18's input projected at THIS computed call. All remaining observations
come from the same input; no reserve/capacity/allocator success is manufactured.
Identifying this projection with a native input remains an OPEN bridge. -/
def atCallInput (i : TupleInput) (priorCalls : List CompletedCall) (children : List Scalar) : TupleInput :=
  { i with journalPresent := (atPositiveTuple priorCalls children).arena.isSome }

theorem selected_call_not_active (i : TupleInput) (priorCalls : List CompletedCall)
    (children : List Scalar) :
    (atCallInput i priorCalls children).journalPresent = false := by
  simp [atCallInput, selected_call_arena_absent]

/-- Applied to the exact R18 predicate, not a replacement local predicate.
This excludes the seven-event premises only for the computed selected model.
It proves no five-event bound and authenticates no native caller. -/
theorem selected_call_excludes_R18 (i : TupleInput) (priorCalls : List CompletedCall)
    (children : List Scalar) :
    ¬ Conditions (atCallInput i priorCalls children) := by
  intro h
  have active := h.activeJournal
  rw [selected_call_not_active] at active
  cases active

end YulangClosure.FormalPermissionCandidateCallJournal
