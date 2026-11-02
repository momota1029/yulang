# R246: production error propagation and extrusion lifetime

Status: **candidate static source evidence; fresh independent review pending**.
Revision 1. Author: `/root/sol_r246_error_lifetime`; no coauthors/descendants.
Contract: `tasks/agent-loop/sprints/production-error-lifetime-r246.md`, SHA-256
`e5319ef4faea4da5f57b39299e2557d1986b8bd2230d0392d6e85ee41bb10dd3`.
Baseline: `2c70049839210df7f12e3d3d68b17f1908ed897b`, observed by read-only
`.git/HEAD` and its `refs/heads/yulang3` file, without a Git command.

## Claim and application

The unchanged parent is Yulang inference soundness and its Rust implementation,
with the accepted source domain, original Simple-sub A/B obligations, shared
witnesses and arbitrary independent satisfying assignments. The immediate edge
is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / `R70-ENTRY-WF-1`; R245 states its
remaining lifetime obligation in §3. No source restriction, selected assignment,
F1/FK1 identification, foreign-continuation argument or semantic change is made.

The source argument establishes the following bounded claim for the pinned
non-test call graph, including feature-enabled candidate/research entrypoints:

```text
R246-EXIT
For every actual session S owned by one of the production consumers below,
if a route transaction attempt returns SolveAvailabilityError,
then the remaining control flow for S does not invoke candidate_extrude,
prepare_candidate_fresh_use, or freshen_candidate_graph_core.
It returns an error and discards S; one observation consumer may first read
immutable readbacks and an outer wrapper may return those readbacks as Ok.
```

This is an informal source result, not a Lean declaration or an executed
transition theorem. Lean theorem type and axiom dependencies: NOT APPLICABLE.
Checker NOT RUN under the source-only contract. No runtime/probe result is
claimed. The quantified source set is the actual consumers at the verified
bytes, not arbitrary future uses of private `&mut InferenceSession` methods.

Apply this at R245's §3 edge: there is no current non-test history consisting
of a failed route transaction, reuse of its session, and a later ordinary
extrusion at `lib.rs:14822` or `14835`. Therefore the post-rollback survivor
equation is **excluded by absence of that continuation**, for every listed
reference kind. It is not proved by showing lookup succeeds, nor by assuming
that journal rollback preserves owner identity. Under the assignment's explicit
condition, no retained-owner/journal equation is derived: no continuation to
which such an equation must be applied was found.

**Parent delta zero.** This removes the failed-route/later-extrusion branch
from the current source application of R245, subject to independent review.
It does not derive all of WCurrent. Validity of captured inputs and their
preservation along successful histories, all remaining producer/consumer
premises listed in R245 §3, R71 raw-slot/canonical-fiber coverage and later
queue execution/acknowledgement remain independent. The full entry and the
full inference parent remain OPEN.

## 1. Transaction boundary: errors remain errors

`lib.rs:9332–9551` defines the Fresh begin/wrapper. A failed begin returns
before the operation is called. Its partial store setup is undone at
`9442/9446/9475/9479`; this fact is not used as a lifetime theorem.
`finish_route_transaction` (`9554–9560`) selects failed-candidate sampling
from the journal purpose and delegates to the common finish owner.

`finish_route_transaction_with_candidate_accounting` (`9563–9614`) has exactly
two result arms. `Ok(value)` commits the context replay operations and store,
and can publish a completed LocalUse. `Err(error)` calls
`rollback_route_transaction()?`, optionally samples resources, then returns
`Err(error)`. If rollback or sampling itself fails, `?` returns that error.
None of these branches turns an operation error into successful inference.
Rollback's fallible refresh/cursor checks (`9711–9770`) therefore do not create
a retry branch either. No completeness claim about their inverse writes is
needed for R246-EXIT.

All operation results here are `SolveAvailabilityError`. Ordinary solver type
diagnostics in the session's error vector are distinct: successful inference
may retain diagnostics and continue through an `Ok` transaction. R246 does not
exclude or weaken those successful histories.

## 2. Exhaustive production transaction call sites

Name searches across `crates/yu-solver/src/**/*.rs` located transaction start,
finish, rollback, wrapper and caller symbols. Actual definitions and enclosing
`cfg(test)` boundaries were read; filename filtering alone was not used to
classify production. There are five non-test operation call sites outside the
shared wrappers:

| Transaction site | Actual immediate consumer | Result behavior |
| --- | --- | --- |
| `lib.rs:18318`, `route_internal` | Ordinary SCC loop `17305`; candidate open use `candidate_scheme.rs:4438`; receiving assembly `candidate_receiver.rs:5587` | Tail-returns wrapper result; every listed consumer uses `?` or tail return |
| `lib.rs:19242`, `route_incoming` | Ordinary SCC incoming loop `18297`; candidate graph-plan incoming loop `candidate_scheme.rs:3300`; source `Action::Module` at `candidate_source.rs:2506` | Cleanup/accounting wrapper preserves error, then each caller uses `?` |
| `candidate_scheme.rs:5270`, `route_candidate_local_run` | `route_candidate_local` at `5228`, then source `Action::Local` at `2510` | Begin/finish chained by `and_then`; result returned after flag/scratch cleanup; both consumers use `?` |
| `candidate_effect.rs:1351`, `candidate_catch_operation` with `h_arg = Some` | Source `Action::CatchOperation` at `candidate_source.rs:2513` | Tail-returns transaction; action uses `?` |
| `candidate_effect.rs:1461`, `candidate_field_bound_v1` | Source `Action::FieldBoundV1` at `candidate_source.rs:2514` | Tail-returns transaction; action uses `?` |

CatchOperation without `h_arg` (`candidate_effect.rs:1353`) invokes the inner
operation directly and is not a hidden transaction. The inner operation saves
its result, drops signature scratch/keepalive objects and returns `admitted`
(`1449–1458`); this cleanup does not swallow an error. FieldBoundV1 has no
alternative catch branch.

The incoming wrapper deserves separate treatment (`lib.rs:19227–19318`). It
can continue *accounting* after the transaction returns an error. Its post-
rollback sample can replace that error with another availability error. The
`sample_result.and(result)` return cannot produce Ok when `result` is Err;
the final event-sample branch returns IdentityExhausted or the original result.
It does not call a solver drain, FreshUse constructor or extrusion afterward.
The ordinary `route_incoming_inner` restores its temporarily moved finalizer
and instantiation scratch before returning its saved result
(`19447–19607`); failure sampling also only preserves/replaces an error.
The candidate branch tail-returns `route_candidate_graph` (`19454`), whose
saved result is returned after restoring scratch (`candidate_scheme.rs:4458–4467`).

Local routing passes `pause_after = None` in production (`5228`), and non-test
code asserts that condition (`5265`). Its temporary LocalUse pop is reversed
before `result?` (`5318–5325`); cleanup at `5331–5336` returns the saved result.
Post-success role/field activation at `5230–5255` can also fail; those errors
propagate through the same source consumers. No rollback continuation is
created by that successful-transaction/error-after-commit case.

## 3. Actual caller graph to session consumption

**Ordinary SCC execution.** Internal and incoming route errors leave
`execute_scc_plan_inner` at `lib.rs:17305` and `18297` respectively. The wrapper
at `17178–17196` returns its result; candidate-only scratch cleanup in its other
branch likewise returns its result. `execute` calls the wrapper with `?`
(`10708`). `run(mut self)` calls `execute()?` before consuming itself in
`finish` (`10732–10735`). Its public entries, `SolvedModule::solve` (`20388`)
and optional shadow-capture solve (`20418`), transfer the session into `run`.
An execute failure returns from that consuming invocation; no session is
returned in the error and no finalization/inference continuation follows.

**Candidate open and incoming routes.** `route_candidate_open_use`
(`candidate_scheme.rs:4432–4438`) validates the active use and tail-returns
`route_internal`. Its graph-plan call at `3199` uses `?`; graph-plan incoming
at `3300` uses `?`. The candidate branch of `execute_scc_plan` returns that
plan's error (`lib.rs:17181–17187`) to `execute`'s `?`.

**Source schedules, including Local and operation-v1.** The action dispatcher
(`candidate_source.rs:2469–2520`) uses `?` for both Module variants, Local,
CatchOperation and FieldBoundV1. Its only non-test consumers are the source
stepper (`2459`) and receiving assembly (`candidate_receiver.rs:5589`). The
stepper increments `source.next` only after action success (`2466`). The drive
loop uses `step_candidate_source(support)?` (`2395`). The synchronous schedule
owner calls `drive_candidate_source(Support::READY)`, clears the source frame
on Err, then applies `result?` (`2358–2367`). Clearing that frame is cleanup,
not resumption.

All four synchronous schedule adapters return their schedule result:
Expression (`2329–2337`), Member (`2339–2349`), Loose (`2351–2352`) and Root
(`2354–2356`). Their actual consumers are:

- Root: candidate graph-plan member loop (`candidate_scheme.rs:3192`), `?`.
- Member: candidate graph-plan member construction (`3306`), `?`.
- Expression: operator-provider construction (`3471`), `?`, called by the
  graph-plan order loop (`3161`), also `?`; and `execute`'s expression loop
  (`lib.rs:10722`), `?`.
- Loose: `execute` (`10712`), `?`.

The driver can represent `CandidateRun::Suspended` as Ok, which is a different
result from an availability error. Production synchronous callers supply
READY and have no synthetic registration; their suspended arm is unreachable.
The support-registration constructor in this path is test-only (`2383`).
No successful suspension is relabeled a failed transaction.

**Consuming candidate convenience method.** `run_candidate(mut self)`
(`lib.rs:10738–10743`) uses `execute()?`, then field-tail execution `?`, then
consumes itself in `finish_candidate`. Its body cannot continue after either
error. The actual caller search finds its invocations in test code, rather
than in the non-test public CandidateInference solve path. R246 does not invent
a production caller for this method merely because it is compiled.

**Actual public CandidateInference solve path.** The solve variants at
`shadow_apply.rs:1584–1644` reach `solve_hirs_mode_with_role_sources`
(`1755`). It privately creates the session at `1833`. With no readback sink,
`session.execute().map_err(...)?` (`1922`) returns immediately on error. Only
success reaches field-tail execution; its error branch returns an error
(`1923–1930`), possibly remapped to MissingMemberSource using an immutable
query. Only complete success consumes the session in `finish_candidate`.
Thus the actual path is not inferred from the separate run_candidate body.

**Receiving-residual experiment.** This is another real non-test caller,
outside `execute`/`run`. `execute_receiving_assembly` applies `?` directly to
route_internal and execute_candidate_action (`candidate_receiver.rs:5587/5589`).
Its sole caller, `solve_receiving_residual_experiment`, privately allocates a
session, calls the assembly with `.map_err(...)?`, and only then moves it into
ReceivingResidualExperiment (`3155–3178`). An assembly failure leaves before
that move. Failure of subsequent authenticated publication also returns before
the experiment can escape. The successful retained experiment is not a
failed-transaction/retry history.

## 4. Non-test error observations do not resume inference

The readback-enabled solve branch explicitly matches `session.execute()`
(`shadow_apply.rs:1849`). Its `Err(DeferredSelectionUnavailable)` arm
(`1908–1917`) reads receiver/captured-member evidence, records a graph count
snapshot, then returns the same error. Other execute errors return directly
(`1918`). It does not invoke field-tail execution after execute failure.

If execute succeeds but field-tail execution fails with DeferredSelectionUnavailable,
the branch at `1874–1889` similarly collects readbacks and returns. Other
field-tail errors return directly. The pending-selection branch (`1892–1904`)
also observes and returns; it does not retry dispatch.

The post-error methods are immutable session queries:
`candidate_field_tail_receiver_readbacks(&self)` (`lib.rs:12266`),
`candidate_captured_member_field_tail_readbacks(&self)` (`13552`),
`missing_candidate_member_source(&self)` (`candidate_scheme.rs:4391`) and the
local `record_graph_snapshot(&InferenceSession, ...)` (`shadow_apply.rs:1834`).
`candidate_extrude` requires `&mut self` (`candidate_extrusion.rs:24`); the
error arms themselves have no later mutating inference call. The privately
owned session is discarded when the solve helper returns. No session/reference
to it appears in the returned CandidateError or owned readback value.

The outer public inspection adapter at `shadow_apply.rs:1622–1635` may convert
that DeferredSelectionUnavailable into **Ok(readbacks)** when useful evidence
was collected. This is genuine API-level error absorption. Its callee has
already discarded the solver session; it cannot reach later extrusion in
that session. Excluding this branch merely because execute returned Err would
have been insufficient; the readback, return and ownership path are essential.

Field-tail's internal `FieldTailMemberSelection::Unavailable` branch
(`candidate_scheme.rs:3910–3916`) queues a deferred descriptor and continues.
That value is a selection result, not an absorbed route-transaction Err.
Its fallible FreshUse/admission calls (`3960–4020`) use `?`; failed helpers do
not become continued loop work. This distinguishes real descriptor deferral
from the unavailable transaction continuation asked about here.

R246-EXIT concerns later inference consumers. It does not certify arbitrary
post-error readback consistency, memory safety of all code, or complete abnormal
restoration; those stronger conclusions do not follow from this call graph.

## 5. Test-only retained continuations

Both explicit RetainedResume transaction starts are excluded by their owning
attributes, not by their names:

- `resume_typed_drain_route` (`lib.rs:14528–14534`) has
  `cfg(all(test, feature = "shadow-apply-candidate"))`.
- `candidate_test_retained_local_step` (`candidate_scheme.rs:5396–5434`) has
  `cfg(test)` and can deliberately fail after one retained step.

`candidate_test_local_script` (`5338–5394`) is cfg(test). Its DriveOne passes a
pause budget; FailOne (`5363`) deliberately commits an operation result to an
Err transaction while retaining the test session for later steps. The production
Local caller passes no pause budget and cannot receive Paused.
The tests beginning at `candidate_scheme.rs:5483`, `candidate_effect.rs:2828`,
`candidate_source.rs:2524`, `candidate_receiver.rs:5703`, and lib's enclosing
test modules (including `21016`, `21210`, `36346`) contain direct private calls,
failure injection and reruns. For example `candidate_scheme.rs:6063–6071`
forces failed Local publication then drives the same retained source frame.
That is not a production source schedule consumer. No such test was executed.

## 6. Lifetime disposition, reuse and remaining work

For R245's captured RowKey, structural Term, view/member/tail/payload tuple,
relation/context/scoped ID and replay/restoration owner/head references, the
following disposition is uniform: their validity after rollback is **not
established by an owner equation here**; their later FreshUse/extrusion use
after a failed production transaction is excluded by R246-EXIT. Readbacks are
separate, immutable observations followed by session disposal. No non-test
continued inference path was found, hence no route-specific survivor equation
or source-qualified dangling-reference counterexample was constructed.

Reuse R245's frozen local native-output equation, actual current constructor
inventory and conditional return result at their existing premises. R246 adds
the control-flow reason that a discarded failed attempt cannot supply a later
extrusion entry. Reject the proposed need to prove complete rollback solely
for those discarded attempts; the governing October 11 abnormal-path rule
requires only meaningful continued work. Also reject inference from Err alone,
test retries as production evidence, successful lookup as owner identity, and
the assumption that rollback function bodies by themselves prove preservation.

Next source/proof step belongs to Luna: apply this reviewed exclusion to both
R245 call+ and call- derivations, then address their remaining successful-
history captured-input/producer validity premises at Capture::row/expand_node,
prepare_candidate_fresh_use and the actual row/view/context producers. Keep
R71 and queue acknowledgement/settlement assigned separately. No new lifetime
theorem or semantic weakening is authorized by this note. Falsifier of the
bounded result: a non-test consumer at these bytes absorbs a transaction Err,
retains that same InferenceSession, and reaches an actual later candidate_extrude
call. A newly added caller must be audited before reusing the exclusion.

Implementation: **NO_SAFE_CODE_SLICE**. Actual owners inspected include
route_internal/route_incoming and their accounting/rollback consumers, Local
routing, CatchOperation/FieldBoundV1 and both public candidate consumers.
No reachable post-error extrusion defect was demonstrated; no production
edit is justified. Independent review/adjudication and shared state/Git remain
Luna's responsibility, not this producer's certification.

## 7. Frozen inputs and execution receipt

All 13 final contract table pins were recomputed with SHA-256 and MATCH before
source claims. The exact pins are:

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956  tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md
7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e  notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md
647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322  tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md
```

Initial baseline gate stopped: contract declared
`64dcbc150aec64f7a17abb08171f4cea48c84ce8` but read-only ref inspection saw
`2c70049839210df7f12e3d3d68b17f1908ed897b`. Luna confirmed its own admission
checkpoint caused the change and revised only the baseline; hash
`284689792038836006602595282e47ac32b13fc839ff17c35c3f3f526256b63e`
and the baseline were revalidated before resumption. Searches then located
three unlisted production owners. Luna explicitly admitted their pins before
body citation, producing the final contract hash above. No worker scope,
write lease, source meaning or budget was enlarged.

The R245 frozen dependency appendix was additionally hashed: 23 of its 24
records MATCH. Its historical mutable administrative admission record changed
from `77bd3c3ea324caf3c6d4b876ce204f83e6086363e09bfe51b49a76b99a4d8fb4`
to `06da4c9da2cfde6ef33e3a49c71dd7b4bcd49a6b076d543ff2c81a76952bbeb9`.
Luna confirmed its later outcome/review append and explicitly excluded that
record from semantic dependencies. It is not cited to establish a proof,
review, authority change or source fact here. The frozen R245 theory/handoff
and all actual source pins remain unchanged. No claim that all historical
appendix bytes still match is made.

Requested model/effort: gpt-6.1-sol/high. Effective observed model/effort:
UNKNOWN; no in-place switch. Budget: at most 1800 active seconds, no renewal;
exact active seconds/CPU/RSS UNKNOWN, full reservation retained. Clock reading
2026-11-02 03:36:17 UTC is an observation, not a complete active-time receipt.
Checks: static reads/searches, SHA-256, read-only ref lookup and output
whitespace/dependency recheck. Initial `python` command was unavailable;
`python3` hashing succeeded. Some rg no-match searches return exit 1; no
compiler/checker failure is inferred from that. No builds, tests, Lean, Cargo,
probes, caches, scratch files, production edits, runtime/quarantined-path
access, descendants, external contact or Git commands/mutations.

All new/written paths are exactly this note and
`tasks/agent-loop/inbox/production-error-lifetime-r246.md`.
Revision 1 frozen after final read-only checks. **STOPPED / WRITES_STOPPED**;
NO_DESCENDANTS; scratch/generated paths NONE. No continued worker activity is
implied by pending independent review.
