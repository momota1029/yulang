# Oracle direct/provider: specialization records and the attachment boundary

Date: 2026-10-12
Status: frozen complementary source audit; unreviewed; M and original H OPEN
Claim class: bounded source characterization and exact missing typed boundary contract
Assigned Y3 baseline: `e52400a52bf490d8fb8ec1cc1bc03e8b008c1801`
Assigned Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation or Git

## Objective and authority

Audit M from [the frozen counterexample attempt](../theory/2026-10-12-oracle-direct-provider-hygiene-counterexample-proof.md)
§5: join provider ping's actual ApplicationArgument contribution through the
typed provider/cb/direct-return/outer-App adaptation and force route to complete
output, while establishing its attachment status against direct's annotation
a and its fresh SubtractId image alpha_u. The original [H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1 retains every source, occurrence, scope, use and output-route quantifier.
This lane does not repeat poly lowering, inference R or its cancellation proof.

Governing meaning remains annotation-effect-hygiene-integration §§1–2,
contextual-attachment-admission-design §§1,3 and top-level inference principles
§§1–5. Origin inequality is not attachment independence. The absence of a
source Catch is not evidence that a thunk is forced. No source restriction,
new semantic interpretation or production representation is selected.

Hypotheses for source facts: the inspected pinned source bytes and normal
completed calls without allocation/resource failure. These do not assume a
SolvedTask for the discriminator, successful specialization, selected adapters,
provider force, attachment independence or complete-output adequacy.

## Authentic same-task constructors and records

Oracle locators below are relative to its read root.

| Owner | Actual construction and retained evidence | Boundary of the fact |
| --- | --- | --- |
| `crates/specialize/src/specialize2/task_solver.rs:29–51,142–178` | `solve_def_body` solves the body against its actual signature; materialized occurrence lookup obtains sidecar anchors and completeness for the original owner/role. Missing occurrence lookup returns Incomplete. | An anchored typing comparison is not an event-specific contribution attachment. |
| `specialize2/task_solver.rs:479–605` | Ordinary Apply consumes the actual argument according to the same callee's Function ports and joins callee/argument/return Effects. EffectOp Apply separately instantiates its actual operation scheme and constructs its runtime shape. | This constructs typed requirements; it does not execute an operation or select the emitted force path. |
| `specialize2/type_graph.rs:121–145` | Materialized subtype entry retains root lower/upper anchors and their completeness in specialization provenance. | Source/proof anchors do not identify a runtime request or classify attachment against alpha_u. |
| `specialize2/task_solver/finish.rs:131–180,238–246`; `specialize2/mod.rs:179–231` | Finish resolves actual/consumer types and ref signatures in one task. `SolvedTask` retains these maps, actual/consumer slots, raw-thunk membership and a runtime evidence graph. | A poly inferred scheme is not this task. The discriminator's actual solved maps have not been supplied. |
| `specialize2/runtime_evidence.rs:1546–1616,1704–1840,1953–2102` | Task/node/site records retain expression IDs, operation Def/path, App children, boundary types/slots, stack weights, weighted graph edges, subtraction demands and residuals. BoundaryCandidate records `function_like` and `argument_contract`. | These are source/type-site records. No inspected field records whether ping's eventual output is attached to a/alpha_u. The exported graph schema does not export TypeGraph's detailed subtype-provenance record list. |
| `specialize2/emit.rs:112–195,246–278,377–421` | Instance selection retains def and inference/runtime/marker signatures, solves that body, records its task, emits source Apps and chooses Local, EffectOp or specialized InstanceRef from that task. | Exact actual/consumer/ref signatures determine the discriminator's instance and adapter choices; printed poly types do not supply them. |
| `specialize2/emit.rs:340–350`; `crates/mono/src/lib.rs:175–184,227–243` | A recognized source App receives `ApplicationProvenanceTag { task, poly_expr }`. The tag is sparse lowering identity and is skipped by serialization. | This provides an in-memory App/task join, not a provider-origin/annotation/request attachment record. |

The runtime-evidence static-route facility is also bounded. Its route records
contain operation expression, Apply/callee, operation Def/family and static
handler or dynamic reason (`runtime_evidence.rs:61–85`). The source traversal
marks application-argument and callback-shaped boundaries as delayed/hygiene
boundaries (`:377–480,537–584`). It does not certify that an operation in a
returned callback is executed. A route candidate is not a ForceThunk witness.

## Adapter, force and Request consumers

`emit.rs:809–1057` and `runtime_shape.rs:875–924` use actual and expected
types to select identity, FunctionAdapter, thunk construction/force, cast or
Unsupported/UnsatisfiedSubtype paths. Consequently one cannot omit these
boundaries or substitute an independently selected pure/provider signature.

The available hygiene carrier is concrete but has different coordinates:
`poly/src/expr.rs:148–163` defines ArgEffectContract markers by path, depth
and resume policy. `mono/src/lib.rs:151–172` defines adapter GuardMarkers by
path, depth and guard/resumption flags. `specialize/src/hygiene.rs:15–93`
derives adapter marker plans from source/target types and that argument contract.
These fields do not carry a, provider origin b or alpha_u.

Runtime consumer facts are exact:

- `mono-runtime/src/runtime/eval.rs:4–96` dispatches on `expr.kind`, not the
  sparse source-provenance tag. A MakeThunk stores its body/environment;
  ForceThunk evaluates its thunk and invokes the actual force consumer.
- `runtime/flow.rs:74–136` binds actual closure arguments and adapts an
  adapter's argument and result around its actual underlying function,
  installing the concrete marker plans.
- Applying EffectOp creates `Thunk::Effect { path, payload }`
  (`runtime/flow.rs:29–32`). Only the reached force case creates a Request
  (`runtime/thunk.rs:117–126`, `runtime/flow.rs:136–153`).
- `runtime/flow.rs:391–414` allocates fresh runtime GuardIds for marker plans.
  `mono-runtime/src/lib.rs:55–62` records Request path, guards, handler
  boundary, payload and continuation. No inspected constructor maps those
  GuardIds or that Request to the inference SubtractId alpha_u or origin b.

These are conditional operational facts, not a derivation that the exact
specialized source selects ForceThunk or produces a ping Request. Lack of
those fields does not prove a correspondence theorem impossible: such a
theorem could establish the interpretation from construction history.

## Smallest remaining typed boundary contract

M is not established by the inspected records. Its missing contract is:

> For the actual same-task signatures and emitted instances of this source,
> interpret each selected provider/formal/result/outer-App boundary jointly,
> preserving the original provider contribution and its attachment status
> against a/alpha_u. Show what the selected adapters and thunk boundaries do
> to that contribution, and establish its reached force/complete-output
> observation or an authentic specialization rejection.

The attachment interpretation must connect inference/source coordinates to
the actual marker/request/continuation history. The force/output premise must
come from the selected emission and runtime consumers. Unequal origins,
same-family support, an OperationCall site, a raw-thunk flag or a handler-route
candidate supplies neither conclusion. This is a localized source/runtime
correspondence obligation, not a genuine newly demonstrated language choice.
H and the counterexample claim remain OPEN; no all-source absence search or
impossibility result is claimed.

One recommended next action: apply the constructive lane to this same-task
boundary adequacy/attachment contract using existing anchored type records
and concrete marker/force owners, without another inference-R probe.

## Checks and snapshot

Checks: bounded `rg`, `sed`, numbered source reads, input and Oracle SHA-256
captures; final note whitespace/link/hash inspection. Initial whole-file
captures truncated; decisive record schemas and consumers were reread narrowly.
Guessed runtime paths under `mono` were absent; actual owners were located
under `mono-runtime`. No Oracle execution, build/test, Git command/mutation,
checker, random seed/range, mutation run or child dispatch. Maximum concurrent
read batch: two lightweight processes; zero heavyweight processes and samples.
CPU/RSS and exact reasoning wall time unknown; bounded 30-minute packet.
No independent oracle or review occurred. This producer does not certify M.

Initial input SHA-256: counterexample attempt
`9cbc06bdf406ea39439d8dca57c343548aa83faf8fff6fff50a6d095d520a88c`.
Final input recheck detected concurrent movement to
`3e548eda14ec0101febdd949733dc2c1fe6ab3770d34892c9bd60668bbeef268`.
Section 5 was reread: its M, typed-boundary and force premises remain the
same; its production entry locator now names `lib.rs:77–82`. This is scoped
dependency revalidation, not certification of other changes in that note.
Oracle byte snapshots:

```text
specialize2/mod.rs              8ccf7a3850384bfe6e0dab024732a830364cb920197b8f75392efc90c68a67a8
specialize2/task_solver.rs      cc534583e8fd154b51e8c857ef7b17df19fe68e9410fd9acb74c1d13cb1d2f66
task_solver/finish.rs           8ee9baf8bdac1ada4efb6f33331efab15e9f2a61674a7c492180ceac7acf0d28
specialize2/runtime_evidence.rs 301c2c26cbe0c562b1d4a6d7d17bb8ce1a43e0ff2331fa782e4a9f7013822616
specialize2/emit.rs             7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c
specialize/src/hygiene.rs       266c05f4c937fc9f9d95cb6b1c435e9ff74181ffc5e8d7719faeefc7a8ff33e4
mono-runtime/runtime/eval.rs    e78f2ba1b1fc1fec696a658bb1f6e56770a00d71b8863e8849dcfcafc724b090
mono-runtime/runtime/flow.rs    83331d4d18066e8361a1ef3f89de2dffeddb7e0e2acb8e910bd5edd44dfffd40
mono-runtime/runtime/thunk.rs   27b6d57ee711dbb7b8bb8da9ec5c05c46ad8ec7f01a29f381664ca3aa4509739
```

Revision pins are primary-supplied; this lane performed no Git verification.
No dependency was edited. Writes stopped before submission.

## Commit packet

Exact leased changed path:
`notes/progress/2026-10-12-oracle-direct-provider-specialization-audit.md`.
Baseline: `e52400a52bf490d8fb8ec1cc1bc03e8b008c1801`.
Dependency hash changes: none made by this lane; the input changed concurrently
from the initial to final hash recorded above, with §5 revalidated. Newly
captured owner hashes above have no separately supplied previous values.
Review status: frozen unreviewed source
audit, M/H OPEN. Checks already run: bounded static source and hash inspection,
final artifact whitespace/link/hash check; no execution/build/test.
Proposed message: `research: audit Oracle provider specialization attachment boundary`.
Shared-record deltas left for primary/curator: record authentic same-task
type/site/App-tag evidence and the marker/force interpretation boundary;
retain attachment classification and complete-output M as OPEN; no semantic,
production or independent-review promotion.
