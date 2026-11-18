# Selected-request validation and terminating checked execution

## Change from cycle261

Cycle261's CandidateValidation.finish checked every Output in the fixed candidate
pool before execution, including pairs never selected by any root. The new modules
check only each current round's actual selected roots and their actual snapshot
requests, using the Plan supplied for that particular state/root. No candidate-pool
Ready premise and no all-state Ready premise is introduced.

The entire selected list is validated before this round's scheduler writes anything.
This includes selected roots whose proposals would be no-ops. It is narrower than
checking all possible pool pairs, not a claim to skip every semantically unnecessary
check. The scheduler remains a pure function; an error returns a diagnostic, not a
partially published state.

## Modules / interfaces

- GeneralRebaseSelectedCheck262.checkRoots: finite recursion over selected roots;
  first actual missing/untranslated body returns an internal Failure containing the
  selected root and existing ClassCheck failure. check_exact iff ReadyRoots;
  error_selected identifies a genuinely selected failing root; actual_ready equates
  ReadyRoots to the existing actual-snapshot readiness predicate.
- GeneralRebaseSelectedSettle262.run: check all selected roots at this state, call
  the existing checked Scheduler.next once, return on terminal/error, otherwise
  recurse on strictly shorter remaining facts. No readiness assumptions are needed
  for totality. Failure.selected and Failure.outside remain internal diagnostics.
- Its Trace records every actual pre-write finite state in order, every visited
  round's selected-root readiness, and terminal readiness plus next=.ok none.
  successful_trace and trace_success give both directions. to_runs and ordinary_settle
  connect this exact execution to the old finite scheduler; certificate adds budget
  and quiescence without assuming universal readiness.
- GeneralRebaseSelectedMeaning262.from_checked extracts the planned event history
  from those same intermediate states and proves actual Ready for every selected
  event. It does not independently choose an unrelated history. certificate combines
  this trace with the all-assignment model/effect equivalence under the explicit
  structural Plan compatibility and request-pool coverage conditions.
- GeneralRebaseSelectedMeaning262.source_certificate additionally derives the pool
  once from actual source Initial formation, then instantiates that certificate for
  an explicitly supplied reachable-snapshot inspector and structurally compatible
  Plan schedule. Actual run success, rather than universal Ready, supplies readiness.
- GeneralRebaseSelectedFailure262.error_path derives a finite-rebase Runs prefix
  from an error of the whole runner to a diagnostic state. selected_provenance adds
  the step budget, actual selected-root membership at that state and the exact
  ClassCheck failure there. Thus diagnostics are not limited to checkRoots at the
  initial round. The theorem is about the finite rebase relation, not a source-Step
  simulation or a complete public-facing rejection explanation.
- GeneralRebaseSelectedRegression262 contains closed regression checks described below.

There are49 explicit named declarations counting structures/inductives as well as
defs/abbrevs/theorems. Their generated declarations are left for the parent's full
cycle audit. No frozen pre-cycle source was changed.

## Regression evidence

1. Same unused missing request `(name1,aTarget)` as cycle261's CandidateBoundaryProbe:
   old fixed-pool validation returns layout.missing, while new run with roots=[]
   returns the input state successfully. The candidate pool itself is unchanged.
2. Stronger nonempty case in GeneralRebaseSelectedUnused262: roots=[focus] selects
   the actual valid merged-leaf requests with the same enlarged pool. From every
   finite state, run returns the state after writing those actual request facts
   (zero or one effective write). From the initial enlarged pool, the unused
   request's self-pair fact remains in remaining. This is proved with symbolic
   key injectivity and support/idempotence, not a giant numeric evaluation.
3. Actual leaf snapshot requests paired deliberately with the parent Plan return
   selected.missing. This tests a compiler-plan mismatch and is explicitly not a
   source-language rejection or a source-reachable Frame counterexample.
4. Correct fixed actual merge snapshot/Plan: the first checked round makes the one
   effective write, the next is terminal, and the selected-only runner returns the
   actual final finite state. The existing historical constraints make this final
   Models predicate unsatisfiable. Translation validation success is not mistaken
   for satisfiability or language acceptance.

## Verification and limitations

All six new modules strictly compiled with Lean4.35.0 using retained dependencies,
`--trust=0 -DwarningAsError=true`. Direct axiom audit and independent standalone
`lake env lean --trust=0 -DwarningAsError=true Audit/Cycle262Selected.lean` both exit0.
Logs: selected-build.txt (source SHA256 and exits), selected-audit.txt and selected-lake-audit.txt.
Reproduce focused compilation with `python3 notes/verification/cycle262/build-selected.py`. Only standard propext,
Classical.choice and Quot.sound occur. No native evaluation or proof placeholders.

The runner may return a selected-body error or unsupported-fact error. No theorem
claims unconditional successful execution without appropriate actual checks. Successful
execution supplies readiness for visited rounds, not every possible finite state.
No compiler is extracted from source, no Frame/packet/Evidence validity is established,
and no arbitrary change of Plan meanings is allowed. No Yulang runtime invocation,
full repository build or independent semantic review of these authored modules was
performed by this worker.
