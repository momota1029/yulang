# Source-generated native interaction — frozen r1

- Sprint: SOURCE-GENERATED-INTERACTION-20261025/r1.
- Contract SHA-256: `013fe582ead230d29fbaa4ab6d977f7b2af3df8cac0db5b5f8efed381fee32c2`.
- Assignment: `/root/source_generated_native_20261025`, handoff revision 1.
- Session: SOURCE-HISTORY-NATIVE-CONNECTION-20261025/root-r1.
- Baseline: `0132d07ca7e149b59f529469d1479a1c8cfa577a`.
- Requested gpt-6-astra/medium; observed model/effort UNKNOWN. Actual worker
  identity comes from the delivered parent task; requested settings are not
  runtime authentication.
- Author: this worker only; no descendants or other contributors.
- Outcome: provisional source/native instrument, execution NOT_RUN by author.
- Exact leases: this handoff and
  `tools/inference-playground/examples/source_generated_interaction_20261025.rs`.

## Parent application and boundary

Original parent: the immutable-extension lemma and `thm:safety` in
`docs/yulang-operational-type-safety-ja.tex`, for every finite sequence of
internal transitions, independently typed external responses, source-generated
fresh extensions and repeated saved-entry resumes. Arbitrary reference sorts,
finite recursive families including zero, RHS/capture typing, exact operation
matching and all arena entries remain in scope. This instrument specializes a
small source witness; it does not restrict or close that parent, the full
paper/native bridge or original Simple-sub A/B.

The example contains two cases, each using the same source structure. A handler
evaluates `my first = k 11; my second = k 23` and adds both results. Before the
request, the delayed body allocates `old = 0` (control) or `old = 5` (capture
distinction). After the request returns into `response`, the suffix allocates
`recur again = if again: recur false else: int_add response old` and calls
`recur true`. Both calls actually traverse the self edge. The source-defined
predictions are `(11 + 0) + (23 + 0) = 34` and
`(11 + 5) + (23 + 5) = 44`. No prediction is reported as an observed result.

The crucial unresolved seam is not only fresh allocation: the pending
`Frame::Local` for `response` retains its original cell and replay writes that
cell again. In contrast, reaching the suffix's `begin_local` anew allocates a
fresh `recur` cell each time. The already-published `old` cell is captured before
the request. The two numeric outputs cannot establish immutable extension for
every native cell, stability of an escaped first closure's response capture,
or preservation of all historical views. Any graph interpretation must account
for the reused pending cell at its actual publication/lookup owners. This
packet neither supplies that relation nor assumes a new versioning semantics.

## Reproduction and expected distinguishing observations

Requested convenient command (build plus up to four executions):

```sh
cargo run --locked -p yu-playground --example source_generated_interaction_20261025 -j1
```

For separate 30-second process limits, the primary can instead perform its one
authorized build, then run these four selectors against Cargo's actual target
directory (shown below for the default target directory):

```sh
cargo build --locked -p yu-playground --example source_generated_interaction_20261025 -j1
timeout 30s target/debug/examples/source_generated_interaction_20261025 zero low
timeout 30s target/debug/examples/source_generated_interaction_20261025 zero public
timeout 30s target/debug/examples/source_generated_interaction_20261025 capture low
timeout 30s target/debug/examples/source_generated_interaction_20261025 capture public
```

Run either the convenient form or the four selectors, not both within the
four-execution grant. Each runtime execution has a 30,000-transition cap.
Low-level stepping additionally checks a 30-second wall deadline; an external
timeout bounds parsing/inference and public execution too. The author ran none.

Low-level expected receipts: `low_status=COMPLETED`, integer 34 / 44, exact
`Machine::steps()`, actual completed handle and SourceSite. Failure, unhandled
request or exhaustion prints its actual outcome and returns a nonzero exit.
Ordinary `yu_playground::execute(..., false)` is compared separately against
`"34\n"` / `"44\n"`. Public rejection is printed as `public_status=REJECTED`
and does not turn low-level evidence into public acceptance. A successful but
different public result is `MISMATCH` and makes the process fail. Public step
counts are explicitly `NOT_EXPOSED`. Exit zero alone is insufficient: inspect
the route status. No successful normal-route claim follows from a rejection.

The instrument reports actual syntax diagnostics, HIR error identities and
attachments, same-HIR candidate identity and conflicts, operation IDs, local
binder IDs/initializer indices, expression constructors/source keys/occurrences,
bounded typed solver fact/origin records, and available local-callee
target/native term records. Unavailable queries remain explicit; completeness
and `preservation_complete` flags are preserved. Candidate conflicts halt the
low-level witness and do not establish a source rejection theorem. The low
route deliberately uses the existing runtime-resume test's
`RuntimeEvidence::default()` path; it is not authenticated production evidence.
No frame, graph state, private cell or owner trace is fabricated.

## Exact constructor-to-consumer owners

| Owner | Construction/equation and consumed identity |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | Retains `LocalSourceBinding.id`, initializer, source/range and expression forms. Name resolution supplies exact local/parameter/catch binder identities. |
| `crates/yu-solver/src/shadow_apply.rs`, `CandidateInference::solve`, `source_occurrence_observation` | Existing candidate constructs/propagates its constraints; observation selects retained provenance facts and origin records by the exact owned occurrence, retains completeness bounds. These rows are structural readback, not preservation evidence. |
| `crates/yu-solver/src/shadow_apply/local_source_observation.rs` | Joins a local-callee Apply to its actual local target, native terms and retained routes. Its preservation-complete flag remains false; query failures are not patched away. |
| `runtime/program.rs:600–765` | Lexical ownership walk marks a local recursive only when its parameterized initializer is active and a Name resolves to that same `HirLocalId`; writes `LocalBinding { id, initializer, recursive }`. Incidental spelling is not the recursion test. |
| `runtime/machine.rs:2500–2547`, `begin_local` | `cell = cells.len(); cells.push(None)` reserves a fresh cell; a recursive binding extends the environment with the exact local ID before initializer evaluation. `initializer_environment` applies existing dispatch handling. |
| `runtime/machine.rs:864`, Lambda | Allocates a closure carrying body, parameter/schema and the current environment. For recursive initialization that environment already contains its reserved self cell. |
| `runtime/machine.rs:1498–1559`, `Frame::Local` | Publishes `Some(ReceivedValue { dispatch, value, interface: Value, view })` at the retained cell. Recursive initialization reuses its extended environment; ordinary binding extends only after publication; then enters `begin_local` for the suffix. |
| `runtime/machine.rs:785–864`, Name; `:2585`, lookup | Resolves the exact binder by following environment parents, selects its cell, reads its current published value, and fails on unavailable/uninitialized state. These are the owners of old-capture and recursive-self read correspondence. |
| `runtime/machine.rs:1211`, Continuation callee; `:1035–1078`, `ResumeArgument` | Internal source continuation application forces the response under its actual invocation, checks the declared response shape, pushes ResumeReturn and enters the saved template with a fresh control map. |
| `runtime/continuation.rs`, ResumeTemplate/TemplateNode; `runtime/machine.rs:1912–2027`, EnterTemplate | The immutable template retains frame/environment handles, not a copied store. Bind clones/pushes the retained frame; Owner reuses active owner or creates a fresh invocation with a per-use control map; Hole returns the actual response. The source suffix subsequently executes the real allocation path. |
| `runtime/machine.rs:599`, `resume_host_write` | Separate host entry checks the currently suspended continuation and marks it resumed once. This example never invokes that API and makes no claim that internal source replay changes host one-use behavior. |

Native private cells, environments, views, templates and owner state are not
exposed by this public probe. A final integer cannot certify their equality or
graph correspondence. The operation-v1 research receipt API is deliberately
not invoked: its specialized callable-response/42 contract is not this source
family's receipt. No use of that API is needed to execute real source replay.

## Frozen bytes and direct dependencies

Example SHA-256:
`18ee279d48f997bf97cf6766f613c2b5f047c44768b528fd6daf0d40d187ca87`.
The handoff's own final SHA-256 is returned separately, avoiding self-reference.

| Direct input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/tests/runtime_resume.rs` | `07ff510f3d29fb831e1767ea42f8f91b591caa6a4d2b1dbff34600cdc7128f91` |
| `tools/inference-playground/tests/runtime.rs` | `f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/shadow_apply/local_source_observation.rs` | `fa7e5a1288eae3ed9093a733645adcac4bd88011802d4fe95fdd10acab2fe66b` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |

Contract/native direct pins were read and matched. No builds, tests, source
executions, format runs, scratch files, Git writes or background processes were
started. Static manual API/source inspection and SHA reads are the only checks.
Pending primary verification and fresh independent review; not commit-approved.

## Remaining premise, falsifier and STOP

TODO `SOURCE-GENERATED-NATIVE-CELL-1`, original parent above, owner primary
source/proof intake: establish the source binder → native environment/cell →
published value → captured/read value → replayed view relation, including reused
pending cells and all retained arena entries. Inputs are the pinned constructor
and consumer equations above and the checked source-history theorem supplied
by the independent proof lane. Required output is an authenticated native
correspondence derivation; this instrument supplies neither that derivation nor
private-state readback. A reused pending cell treated as a globally fresh
immutable node without an established relation falsifies the naive bridge.

Executable falsifiers: source/candidate/program route refusal, runtime failure,
exhaustion, integer other than 34/44, or ordinary-route successful disagreement.
Public refusal blocks a public-route claim. No production repair is authorized.
Rollback owner primary: delete only the example to remove its runtime cost;
there is no added production cost. The handoff is evidence only.

First observed clock: 2026-10-25 09:07:26 UTC. Three stages completed: owner/API
inspection, example construction, frozen handoff. Budget <=900 wall seconds;
no self-extension. Final STOP clock and exact elapsed time are returned in the
delivery message. Writes stop after this handoff; zero descendants, zero
outstanding processes, no unresolved descendant leases. Primary may verify and
review these frozen bytes, then own any explicitly acknowledged repair.
