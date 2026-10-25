# FORCE-PRODUCER-EXPORT-TRACE-20261025/r1

Status: **FROZEN BY LUNA; two source-only assignments issued.** Fresh cap 3,000
seconds, no r8 carryover. This changes the input and owners after repeated
paper-level investigations failed to expose the missing producer equations.

## Original goal and accepted boundary

Original parent: complete Lean proofs of Yulang semantics and type inference for
the original accepted source domain. No scope, quantifier, source, semantic, or
expected-output change is authorized.

r7's `abstract_observe_counted_run_iff` remains CLEAN only for its generic
finite-success statement (Lean hash `620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97`).
r8's N1 and R reports are independently CLEAN only as bounded obstruction
reports; neither source proposition closed. r8 outcome SHA is
`4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb`.
O-NORM, O-RESULT and the original parent remain OPEN.

Source authority and pinned inputs:

- paper `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- N1 obstruction `tasks/agent-loop/inbox/20261025-force-packet-specialization.md`:
  `7492d74c018645394f54559695cc0f7b3278edce2fbd34eb6f20b06504be0f76`.
- R obstruction `tasks/agent-loop/inbox/20261025-force-result-relation.md`:
  `9972764cc9b750fa5fc218b1c571fd29b58ffb46f6a7bc0e566aaaa4e1bfb430`.
- Corrected mapop report remains required when a consumer crosses a matching mapop:
  `203d55dc462046f0616eba027198c68224182fdf4ab03bf19ccb87548c691b8b`.

Exact source-owner snapshot for assignment reads:

| File | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-core/src/shadow_source_annotation_crosswalk.rs` | `9a13b7b46d4d239d00d8f54ed93e6bc58064410bd556ab8f797242f2e87f6d5d` |
| `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |

Baseline `9b945b0bb175e8e0919d388dc720babbdf0c2464` is inherited and not
independently verified. `.git` is read-only. No Git commands or commits are in
scope.

## Proposition N — binder-linked packet export

Target proposition: `binder_packet_export_correspondence`. Trace actual
resolved source binder/use through HIR annotation, local source, solver scheme
and core export/consumer. Establish whether a complete packet carries the
binder correspondence used by type application across profiles, families,
rows, delayed shapes, latent ports, captures, scope/interpretation and identity.
Then trace the actual once-only instantiation operation and consumers. Produce
either (a) a constructor-derived producer/export/consumer map establishing the
correspondence, or (b) the first concrete artifact/edge where a required
coordinate is absent or reinterpreted, with exact owner and falsifier. Distinguish
actual data from shadow proposals and test models; don't infer source semantics
from test names or comments. Do not claim r7's arbitrary `inst` is instantiated
by this path unless the actual producer and consumer relation is derived.

Exact read set (additional narrowly necessary callers may be named, not silently
assumed):

- `crates/yu-hir/src/module/source_annotation.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-core/src/shadow_derivation.rs`
- `crates/yu-core/src/shadow_source_annotation_crosswalk.rs`
- `crates/yu-core/src/shadow_call_formation.rs`
- `tools/inference-playground/src/scheme.rs`

Exact sole output lease:
`tasks/agent-loop/inbox/20261025-binder-packet-export-trace.md`.

Grant: 1,000 seconds, source inspection only. No Lean, tests, builds, native or
compiler execution, code edits, scratch, Git, or descendants.

## Proposition R — Force normal-leave producer

Target proposition: `force_normal_leave_producer_correspondence`. Trace actual
code formation → delayed execution → `return_value` / execution-view completion
→ returned view. Account for allocated occurrences, inherited images, source
schemas, result provenance, all latent paths, suspension and current-resumer
reconstruction. Distinguish generic Force realization from any restricted
RootComp/callback behavior. Produce either (a) a concrete constructor trace
binding actual operand, body return and output occurrences and the corresponding
source-derived result transport domains/images, or (b) the first exact missing
field/edge and its owner. A runtime image dependency alone does not establish
the operational theorem's equations or source authority.

Exact read set:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/continuation.rs`

`tools/inference-playground/src/runtime/dispatch.rs` may be inspected only to
trace direct producer/consumer calls. Other reads must be justified by an
identified direct caller and recorded in the handoff.

Exact sole output lease:
`tasks/agent-loop/inbox/20261025-force-runtime-return-trace.md`.

Grant: 1,200 seconds, source inspection only. No Lean, tests, builds, native or
compiler execution, code edits, scratch, Git, or descendants.

## Parallelism, review and resources

N and R are independent source traces and may run concurrently. Three legacy
UNKNOWN reservations remain quarantined. At most two new authors run at once;
reviewers start only when an author STOP releases capacity. No children.

One fresh independent `compiler_referee` reviews the first frozen artifact and
then the second, up to 500 seconds aggregate, covering producer fields, actual
consumer path, source-vs-provisional boundary, stated missing edge and exact
falsifier. The reviewer is not either author. Luna adjudicates and writes the
outcome: 300 seconds. No Lean lease or checker grant is issued by this contract.

Total: **1,000 N + 1,200 R + 500 fresh review + 300 Luna = 3,000 seconds**.
Unknown exact elapsed time charges the full assignment grant. Successful
source tracing is the outcome, not a theorem proof or permission to modify
compiler semantics.

## Stop and application

Stop on exhausted grant, changed pinned dependency, uncertain source owner, or
an alleged producer that is only proposed/shadow/test scaffolding. Preserve
exact hashes, source locations, actual callers, authorship, model observations,
falsifiers, omitted paths and STOP receipts. A bounded implementation/export
gap can be accepted as such; it does not prove the source semantics impossible.
If accepted source rules still do not select the packet equation, return that
exact equation for semantic authority. Never manufacture a source construction
or resolve ambiguity by data layout.

The output decides what the next direct source/Lean proposition can legitimately
use. No N1/O-RESULT Lean phase, `ForceReturnRows.lean`, production edit, native
run or parent closure follows automatically. O-NORM/O-RESULT remain OPEN until
their original source/native obligations are established and reviewed.
