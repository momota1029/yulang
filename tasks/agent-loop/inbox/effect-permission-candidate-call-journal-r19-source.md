# R19 source trace — ordinary selected candidate root / formal tuple annotation

Status: primary source inspection; conditional on the explicitly selected source schedule below
Sprint: `EFFECT-PERMISSION-CANDIDATE-CALL-JOURNAL/20261030-r19`
Frozen owners: `candidate_source.rs`  
SHA-256 `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `candidate_scheme.rs`  
SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.

## Selected path and source restriction

The selected call is one ordinary selected definition root in an inference
session whose candidate source is active. Its reached `Action::FormalAnnotation`
has an outer nonempty tuple annotation whose elements are collected scalar
leaves (`Bool`, `Str`, `Int`, or `Unit`); it has no top-level effect annotation.
The selected root has no source-level wrapper or top-level effect annotation
before the lambda action. This is a conditional trace for that selected action,
not a universal claim over all source modules, preceding roots, or callers.

The ordinary path is `InferenceSession::execute` (`lib.rs:10598+`) →
`execute_scc_plan` (`lib.rs:17069+`) →
`execute_candidate_graph_plan` (`candidate_scheme.rs:2898+`) →
`execute_candidate_source_root` (`candidate_source.rs:2354+`) →
`begin_candidate_source` / `drive_candidate_source` / `step_candidate_source`
(`candidate_source.rs:2369–2455`) → `execute_candidate_action` →
`candidate_formal_annotation` (`candidate_effect.rs:1877+`). The graph-plan
branch directly invokes the source root; it does not wrap it in
`with_route_transaction`.

## Journal-state transition

1. `InferenceSession::try_new` initializes `route_journal: None` (`lib.rs:10196`).
   `try_new_candidate` calls `try_new`, then `start_candidate_graph`; graph
   initialization does not begin a route transaction (`candidate_scheme.rs:2316+`).
2. `Session::execute` calls `execute_scc_plan` before candidate loose or
   expression schedules. In candidate graph mode, `execute_scc_plan` dispatches
   directly to `execute_candidate_graph_plan` (`lib.rs:17069–17083`).
3. For each dependency-first component, the graph plan sets active roots/uses,
   then executes every member root with `execute_candidate_source_root` directly
   (`candidate_scheme.rs:2898–2950`). There is no transaction wrapper at this
   boundary. `execute_candidate_source_root` starts a synchronous source frame;
   `step_candidate_source` dispatches each action directly and advances the
   schedule cursor only after the action returns (`candidate_source.rs:2354–2488`).
4. At a lambda parameter with the selected annotation shape, schedule construction
   emits `BeginLambda`, then (only for a record pattern) `RecordParameter`,
   then a `FormalEntry` only if `annotation.ty.effects.is_some()`, then
   `FormalAnnotation`. The selected case has no record pattern and no top-level
   effects, so the action prefix at the target site is `BeginLambda` followed by
   `FormalAnnotation`. `term_for_leaf` and primitive preparation occur while
   compiling the schedule, before execution; they do not begin a route journal.
   (`candidate_source.rs:1287–1342`).
5. `BeginLambda` only increments `source_lambda_depth`. The immediately next
   action directly invokes `candidate_formal_annotation`. For the scalar tuple,
   recursive `candidate_formal_value_pair` scalar cases return collected terms;
   the tuple case builds positive and negative tuples via `with_term_events`
   (`candidate_effect.rs:1617–1650`). `with_term_events` drains term-capacity
   snapshots and never begins a route transaction (`lib.rs:10594–10622`).

Route transactions are introduced by `with_route_transaction`, which calls
`begin_route_transaction`, sets `route_journal = Some(...)`, and then calls a
finish path (`lib.rs:9267–9272, 9350–9355, 9418+`). The direct selected root and
action dispatch above do not call that wrapper. Candidate source's ordinary
`Module` action may reach `route_internal` or `route_incoming`; those helpers
wrap each route and finish it before returning (`lib.rs:18207–18209,
18959–18974`). Successful finish takes the active journal; failure paths roll it
back and restore the spare journal, leaving `route_journal` absent. Thus an
intervening completed route does not retain an active journal. The exact selected
prefix contains no Module action. The private/test-only retained-resume entry
`begin_route_transaction_for(RetainedResume)` is cfg-test and is not reachable
from this ordinary production schedule (`lib.rs:14428`). Private transaction
wrappers in candidate helpers/tests are not the selected call.

## Applied R18 consequence and remaining seam

R18's `Conditions.activeJournal` is not supported for this selected ordinary
call if the selected schedule/caller premises above are authenticated: its
route journal begins absent, its immediate prefix has no route wrapper, and
tuple construction uses only `with_term_events`. Consequently the R18
active-journal-conditioned seven-event case is excluded at this selected
positive tuple call. This does not by itself establish all R18 conditions,
capacity observations, allocator results, tuple-child identity, cache miss,
or actual native execution. A Lean proof may derive the logical exclusion only
from a transcription of the stated transition facts; it must not assume the
caller frame or active-journal result as a hypothesis disguised as a theorem.

The source text authenticates a local call-chain and action-prefix argument.
The selected HIR/module instance and graph-plan placement are still explicit
caller facts, not produced by executing the compiler. Other roots, expression
schedules, test/private callers, effectful annotations, nonscalar children,
tuple cache hits and nonempty journals remain outside this packet. Native
reachability, parent soundness and production remain OPEN.
