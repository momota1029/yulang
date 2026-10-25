# Source-generated native interaction — isolated frozen revision 2

Sprint SOURCE-GENERATED-INTERACTION-20261025/r2-isolated; contract SHA-256
`a6c497c11995ebf6ec0078c3890c58f875fbcae6ce0335c28a4213e267241ca8`.
Baseline `0132d07ca7e149b59f529469d1479a1c8cfa577a`. Parent session
`01a17247-73d1-7663-9c3b-ff5b5b9c2ef1`, child session
`01a17250-8b64-7f43-90dd-b056be263a0c`, worker
`/root/source_generated_native_20261025`. Requested gpt-6-astra/medium;
observed model and effort UNKNOWN. Author is this worker only, no descendants.

All paths in this receipt resolve under the exclusive checkout
`/tmp/yulang-source-interaction-01a17247-20261025`. The only write leases are
`tools/inference-playground/examples/source_generated_interaction_20261025.rs`
and this r2 handoff. The original checkout was not read or written during this
resume. The restored r1 handoff remains immutable with SHA-256
`227c601d2bb26186196b421933be91f0e0f78d2c77c8d4df0bd9b8ae0cf0517b`.
It supplies the complete unchanged constructor-to-consumer source inventory
and original parent scope; this revision replaces its case inventory,
execution commands, example hash, refusal exit behavior and runtime receipt.

Outcome: provisional source/native executable instrument, NOT_RUN by author.
No successful source execution or typing preservation is claimed yet.
Example SHA-256:
`d65f979a94001ee393e6075b227c793368231bb9d98c12373db1a758673a0c09`.
This handoff's final hash is returned separately.

## Exact source discriminator

Both cases retain `old = 5` before `io::tick 7`. The handler executes
`my first = k 11; my second = k 23` in order. Each resumed suffix allocates
`recur again = if again: recur false else: builtin_op::int_add response old`.
Each eventual invocation uses `true`, taking the self-reference once before
reading the captures.

| Case | Suffix result | Handler combination | Target |
| --- | --- | --- | --- |
| `immediate` | `recur true` | Adds first and second integers | `(11+5)+(23+5)=44` |
| `escaping` | `recur` | After both resumes, evaluates `first true`, then `second true`, then adds | Independent saved captures: `16+28=44`; shared last-response prediction: `28+28=56` |

The escaping thunk annotation is `[io] (bool -> int)`; the immediate thunk is
`[io] int`. The runtime operation response remains an integer in both cases;
this is not the specialized operation-v1 callable-response research route.

The independent-capture result is the source-to-immutable-graph bridge target,
not an assumed theorem about existing native cell behavior. A result of 56 is
consistent with both closures reading the last response and distinguishes that
prediction from 44; numeric output alone does not authenticate private cell
identities or prove that mechanism caused it. The code preserves unexpected
results and fails its target check without declaring a production compiler bug.
Unavailable syntax/candidate/runtime/public routes likewise remain evidence of
an unavailable witness, not authorization to weaken acceptance or expectations.

## Reproduction within the four-execution grant

From the isolated checkout, the convenient command is:

```sh
cargo run --locked -p yu-playground --example source_generated_interaction_20261025 -j1
```

It attempts both cases through both routes, with no retries. For the primary's
separate 30-second process limits, prefer one build followed by these four
selectors (adjust only the binary location if Cargo uses another target dir):

```sh
cargo build --locked -p yu-playground --example source_generated_interaction_20261025 -j1
timeout 30s target/debug/examples/source_generated_interaction_20261025 immediate low
timeout 30s target/debug/examples/source_generated_interaction_20261025 immediate public
timeout 30s target/debug/examples/source_generated_interaction_20261025 escaping low
timeout 30s target/debug/examples/source_generated_interaction_20261025 escaping public
```

Do not run both forms within this grant. Each runtime attempt is capped at
30,000 transitions. The low route checks a 30-second stepping deadline; the
external timeout also covers parsing/inference and the public call, whose API
does not expose incremental execution or its transition count. A failed
selector does not require rerunning it to obtain evidence; the primary can
continue the other independently authorized selectors.

Low output retains exact `Machine::steps()`, completion handle, integer and
SourceSite, or the actual noncompletion outcome. Public output retains its
actual rendered result or error and marks steps NOT_EXPOSED. Any refusal,
exhaustion or target disagreement yields nonzero process status. In default
all/all mode subsequent independent comparisons still run without retries.
Public rejection no longer exits successfully as it could in r1; no public
acceptance claim follows from the low-level route.

## Construction and consumer correspondence still open

The unchanged source owner inventory in r1 identifies these exact equations:

1. `program.rs:600–765`: the active-initializer lexical walk detects an actual
   self-resolved `HirLocalId` and records `LocalBinding.recursive`.
2. `machine.rs:2500–2547`, `begin_local`: reserves `cells.len()` with `None`,
   extends the recursive environment before evaluating the initializer.
3. `machine.rs:864`, Lambda: stores that actual environment in the closure.
4. `machine.rs:1498–1559`, Local return: publishes `Some(ReceivedValue)` at
   the saved cell, then enters the next source binding/suffix. Nonrecursive
   environment extension occurs after publication.
5. `machine.rs:785–864` and `:2585`: exact resolved binder lookup follows
   environment parents and reads the current cell; unavailable values fail.
6. `machine.rs:1211`, source Continuation callee, and `:1035–1078`,
   ResumeArgument: force/check the real response and enter the saved template.
7. `continuation.rs` and `machine.rs:1912–2027`: templates retain frames and
   environments, not copied stores. Bind replays the retained frame; Owner
   performs the existing active/fresh owner mapping; Hole returns the response.

Thus the pending Local frame for `response` can retain its original cell across
replay, while the later `recur` binding reaches fresh `begin_local` allocation.
The pre-request `old` cell is already published. The native-to-graph relation
must account for the pending-cell publication, captured environments, dispatch
substitution and historical receiving views together; this packet assumes no
compensation and no absence of compensation. The escaping case makes that seam
observable if admitted, while private identities remain unexposed.

The probe retains actual HIR operation IDs, binder/initializer IDs, source
occurrences/keys and constructors. Same-HIR candidate observation exposes
conflicts and bounded typed fact/origin records plus available local-callee
native terms/routes. Completeness flags and unavailable queries are printed.
`preservation_complete` is retained as supplied, never upgraded to a proof.
`RuntimeProgram::from_hir` uses the existing default-evidence research route;
normal `execute` independently prepares its ordinary world/schedule.
Internal repeatable source continuations remain distinct from the one-use
`resume_host_write` check at `machine.rs:599`; neither implementation changes.

Original parent remains the paper's immutable-extension lemma and `thm:safety`
for every finite source-generated extension/repeated-entry history, all relevant
arena entries, arbitrary reference sorts and finite recursive families. This
single recursive family supplies a discriminator, not a narrowed theorem.
Full-paper/native and original Simple-sub A/B remain OPEN. TODO
`SOURCE-GENERATED-NATIVE-CELL-1` remains owned by primary source/proof intake:
prove binder/environment/cell/value/capture/replay-view correspondence, including
reused pending cells. A putative immutable fresh extension mapping that treats
the reused pending cell as unconditionally fresh is not justified by this run.

## Pins, resource accounting and STOP

At resume, restored example hash `18ee279d…` and r1 handoff `227c601d…` matched
the worker's original stopped receipts. The r2 contract and native program /
machine pins matched their contracts. All nine direct source/API/example-test
pins from r1 were re-read here and matched exactly (lib, program, machine,
continuation, runtime_resume test, runtime test, shadow_apply, its local-source
observation module and HIR local_source). No mutable foreign artifact was used.

Checks: source/API inspection and SHA reads only. Zero Cargo/build/test/probe
or source executions, zero formatting commands, zero Git actions, zero scratch
files. Review and execution remain primary-owned. No production semantics,
runtime library, manifest, expectation or test was modified.

Original first clock 09:07:26 UTC; prior STOP 09:10:23 UTC, charged177 seconds.
Resume first clock 2026-10-25 09:17:37 UTC. Additional grant500 seconds, no
budget reset; exact final clock/elapsed receipt accompanies delivery. Logical
stages remain owner audit, witness construction and handoff. Work is frozen
after this receipt; no further writes, descendants, outstanding processes or
unresolved descendant leases. Primary may verify/review the frozen bytes and
own subsequent acknowledged repairs. Rollback owner primary; removing the
example removes all added execution cost, with no production hot-path cost.
