# Source-generated native connection — frozen handoff r1

- Sprint: `SOURCE-GENERATED-INTERACTION-20261025/r1`; contract SHA-256
  `013fe582ead230d29fbaa4ab6d977f7b2af3df8cac0db5b5f8efed381fee32c2`.
- Assignment: native connection, handoff revision 1.
- Baseline: `0132d07ca7e149b59f529469d1479a1c8cfa577a`.
- Worker: `/root/source_generated_native_20261025`; session
  `SOURCE-HISTORY-NATIVE-CONNECTION-20261025/root-r1`; supported launch recorded
  by primary at `2026-10-25T09:07:45.308294+00:00`, followed by active-work ACK.
- Requested model/effort: `gpt-6-astra/medium`; observed: `UNKNOWN/UNKNOWN`.
- Exact leases: this handoff and
  `tools/inference-playground/examples/source_generated_interaction_20261025.rs`.
  Sole author is this worker; no descendants or other contributors.
- Outcome class: **provisional executable instrument, NOT_RUN**. No native
  success or failure has yet been observed by this worker. Primary owns build,
  execution and verification receipts, as explicitly reconfirmed in its ACK.

## Parent application and observation boundary

Original parent: `docs/yulang-operational-type-safety-ja.tex`, immutable-extension
lemma and `thm:safety`, with every finite sequence of internal transitions,
independently typed responses, fresh source extensions and repeated saved-entry
resumes; arbitrary reference sorts and finite recursive families including zero.
This example supplies a concrete executable source at the missing native seam.
It closes no parent theorem, native correspondence, production, or Simple-sub A/B
gate. Its successful execution, if observed, remains source/native evidence.

The one source contains two distinct source applications `k 11` and `k 23` of
the same lexical catch binder. Both returned integers contribute to a sum.
Its delayed main block binds `seed = 42` before `io::tick 7`, binds the response
as `result`, then allocates `loop again`, whose true branch calls `loop false`
and whose false branch computes `seed + result`. It calls `loop true` after
allocation. The arithmetic prediction is `(42 + 11) + (42 + 23) = 118`.
This is a prediction checked by the example, not an observed output in this
handoff. Source values/expectations are not rewritten on mismatch.

The `machine` mode prints parse diagnostics/recoveries; source operation IDs;
definition roots; local binder IDs and initializer indices; Name resolutions,
Apply occurrences, Lambda parameters, Catch binders, and source byte ranges;
candidate same-HIR observation and actual conflict count (first eight conflicts
rendered); then the real runtime outcome, exact machine steps, and completed
value/source site. It stops on failures rather than manufacturing acceptance.
The `public` mode independently invokes ordinary `yu_playground::execute` with
the identical source and checks its rendered result. That API hides step counts;
the example labels them `NOT_EXPOSED`. Each mode executes at most one machine.
No internal frames, cells or environments are exposed, forged or claimed equal.
HIR occurrences distinguish static source sites, not dynamic allocation events.

## Actual source constructor-to-consumer equations

1. `yu_syntax::{parse_file,scan_header}` and
   `yu_hir::shadow::lower_module_with_local_source` retain source nodes and
   `LocalSourceResolution::{Local,CatchBinder,Parameter}` identities.
   `CandidateInference::solve` is observed separately and must return the same
   HIR with zero conflicts before direct-machine execution. This is no proof
   that generated/propagated constraints enforce the parent graph invariant.
2. `runtime/program.rs:607` walks source ownership edges with active local
   initializer IDs; a self-reference to an active parameterized initializer
   enters `recursive`. At `:749` a `LocalBinding` retains its ID, initializer
   label and that recursive flag. Lambda/Apply/Block forms become instructions.
3. `machine.rs:2500` (`begin_local`) appends an empty cell; for a recursive local
   it extends the environment with that binder/cell **before** evaluating its
   initializer. It pushes `Frame::Local { environment, cell, recursive, ... }`.
   `:864` creates an executable closure retaining the current environment.
4. `machine.rs:1498` (`Frame::Local`) writes the received value into the saved
   cell. The recursive branch retains the saved environment; the nonrecursive
   branch extends it after the write. It then calls `begin_local` for the suffix.
   `:2585` lookup follows environment parents and matches the exact binder;
   `:781` Name uses the resulting cell and its stored received value.
5. At `machine.rs:2213`, source handler selection binds an
   `ExecutableValue::Continuation(template)` to the actual catch binder.
   `:1211` source application installs `Frame::ResumeArgument`; `:1006` checks
   the response and enters the saved template with a fresh control map.
   Materialization at `:1865` retains ordinary frames via `frame.clone()`.
   `:1912` (`enter_template`) clones each node: `Bind` pushes its saved frame,
   specially remapping callback `ValueEntry` receiver ownership; `Owner`
   reuses or allocates an invocation and records control renaming; `Hole`
   returns the response. `Frame::Local` cell/environment fields are not freshly
   renamed by the `Bind` branch.
6. Therefore the pending `result` initializer's saved Local cell can be written
   again on replay, whereas reaching the subsequent `loop` binding calls
   `begin_local` again and allocates a new cell. This is a reading of the owning
   equations, **not a dynamic trace established by this example's output**.
   The example consumes the first scalar result before the second replay; it
   does not probe an escaped first closure observing a later pending-cell write.
7. This internal repeated source continuation path is distinct from the private
   `resume_host_write` at `machine.rs:599`: host resume validates the currently
   stopped continuation/operation and host capability, rejects `saved.resumed`,
   sets it true, and supplies Unit once. The example calls no host resume API.

## Exact remaining premise and falsifier

`NATIVE-SOURCE-ENV-REPLAY-1` remains OPEN, owned by primary native/proof intake:
construct a state relation mapping source binder occurrences and recursive
families to actual native cells, closure environments and value graph entries;
prove initialization and Name lookup realize the source RHS/capture typing;
prove each replay of saved Local frames (including writes to a previously
allocated pending cell), fresh suffix allocation, and owner/view/control remapping
preserves the relation and the immutable-extension theorem's old-entry meaning.
Do not identify append-only native arenas with immutable graph contents: native
cells are written. The relation must account for which existing graph entries
can reach a replayed pending cell, including escaped prior closures, and either
establish the required preservation or expose the precise incompatibility.
This one consumed-integer example does not settle that quantifier.

Inputs needed: source typing/capture derivations and authentic saved-template
construction; outputs needed: a reviewed simulation/correspondence proof or an
actual source-qualified counterexample. A binder resolving to another cell,
capture changing contrary to the parent relation, replay overwriting an old
graph observation, missing runtime route, or differing direct/public outcomes
is a falsifier to retain and adjudicate, not a reason to edit expectations.

## Frozen bytes, checks and primary verification handoff

Example SHA-256:
`4a8ac87598e2807f3fc26b1fc6477c7af71f8f5ce1dcbf3e11e568eb10adf33c`.

Direct inputs checked against the contract:

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/tests/runtime_resume.rs` | `07ff510f3d29fb831e1767ea42f8f91b591caa6a4d2b1dbff34600cdc7128f91` |
| `crates/yu-hir/src/module/local_source.rs` (additional inspected API) | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |

Worker checks: read-only API/equation inspection and SHA-256 comparison only.
Builds/tests/native executions: **0**. No generated outputs or scratch files.
No actual runtime outcome, dynamic binder/cell identity, or step count claimed.
Primary may build once after Lean is idle with
`cargo build -p yu-playground --example source_generated_interaction_20261025 --locked -j1`,
then execute the built binary once with `machine` and once with `public`, each
under a 30-second deadline. Each has a 30,000-transition bound. Preserve actual
stdout/stderr, exit code and wall time in the primary verification receipt.
This proposes 2 of the 4 permitted runs; no broad suite or extra build requested.
If either route fails, keep that outcome and stop dependent positive claims.

Worker spent less than 300 seconds of its 900-second grant; no ongoing process.
At handoff freeze: **STOPPED, writes ceased, no descendants, no unresolved child
leases, no Git operations**. Both leased files are frozen pending primary intake
and fresh independent review. Producer does not certify this instrument.
