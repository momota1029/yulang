# CALLBACK-PERMISSION-BRIDGE-20261024 — frozen revision 1

- Sprint/contract: `CONCRETE-CALLBACK-PERMISSION-20261024`, revision 1,
  `4a6b3a6e10d3c496640c015104d555c115e351dd41806f45c04fe6e20fa24f94`.
- Baseline supplied by Luna: `5fbc2c2d9e3ab28032caf599ca024b8ba8b19778`.
- Parent: `SOURCE-SAFETY-BRIDGE`; original Simple-sub A/B claims, quantifiers,
  accepted source domain and native obligations unchanged. Contract's Original
  claim section fixes the bounded `relay(cb: () -> [signal] int)` outcome.
- Outcome class: **source-native-evidence; exact missing runtime transition**.
  Mathematics remains candidate/unreviewed; no code change, execution result,
  source-qualified unsoundness counterexample, reviewed theorem, or production
  authority. Parent remains OPEN_REVIEW; no F1/FK1 or foreign-continuation closure.
- Sole author/actual worker: `/root/callback_permission_prover`. Session UNKNOWN;
  requested model/effort Sol/high; observed model/effort UNKNOWN. No descendants.
  Launch receipt preceded all inspection; Luna acknowledged before work began.

## Result and parent application

Actual HIR constructors retain relay owner `R`, formal `p`, Lambda occurrence
`L`, annotation position `A`, concrete row position `S` and resolved signal
family `E`. Outer Function effects are `None`; result effects are `[E]`.
Candidate admission constructs `FormalPermission(k,L,R,scope,[Result],S,[E])`
with a shared fresh open effect port and ordinary two-way value constraints.
The captured negative Function projection follows `children[2]` to that row.
This retains source permission and open inflow; it is not runtime arrival.

The first missing runtime producer is `RootCompSchema::original_parameter`:
its outer-effects guard rejects this formal, so runtime Lambda is Value with
no schema. `Frame::ValueEntry` preserves the opaque incoming callback view
without a permission boundary. The actual `cb` read creates a genuine relay
receipt but no boundary; `Frame::Callee` opens no Result execution view.

The exact operation callback invocation constructs an inert request carrier,
then `ReceiverReturn` retires its invocation and restores relay owner `r`.
`OperationResultConsumer` subsequently emits event `q` and observes currently
executing views. Thus a permission view ending at the callee return would miss
the event. The same relay Catch requires its active owner `r`, matching resolved
operation/family, authentic same-event observation, same-view owner receipt and
boundary reachability. Its missing grant returns `HandlerEvidence`; absence of
that grant proves no negative protection fact. `primitive::closed_primitive`
rejects relay's Lambda, so that alternative certificate cannot supply authority.

**NO_SAFE_CODE_SLICE:** no safe runtime patch follows under the current lease
until a proof-supported callback-result constructor/consumer encloses the
request-producing `OperationResultConsumer`. This exact obstruction is frozen
for fresh independent review; it is not permission for dependent code writes.

The useful reduction is from a broad callback correspondence gap to three
specific runtime owners: program schema formation, Value-entry receiving
evidence, and the complete callback Result execution/consumer view. No missing
HIR/candidate negative-concrete producer was found in the inspected owners.
Whole-program solver acceptance and full inflow/residual behavior were not
proved or executed. In particular, `write` remains an explicit open obligation
for any implementation; signal permission must never authorize it.

## Artifact, dependencies, and reuse

Frozen artifact:
`notes/theory/2026-10-24-callback-permission-bridge.md`

SHA-256: `c228ff45a272a52b92eaaccd91183272438bb8c3287dd39e7749d700ce919f4d`.

Its Frozen inputs table pins all eleven original contract dependencies, which
matched before and after the audit. Authoritative policy hash:
`a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
The three TeX inputs are research premises; their attributed author is the
originating session's primary agent, sole construction/self-inspection. Source
manuscript `W-Eligible` is unadopted and supplies no runtime authority here.

Luna additionally acknowledged exactly these four read-only local dependencies
after dispatcher consultation; all inspected hashes are pinned here and in the
artifact:

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `tools/inference-playground/src/runtime/primitive.rs` | `eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85` |

The previous partial audit
`notes/theory/2026-10-24-permission-implementation-bridge.md`,
`f9c40e49dd8c4e9ec1c4ef01a0391940ad5c7fd21b27da1c0635501721b6aeed`,
was authored by `/root/source_permission_review` and transcribed by Luna.
Its gap identification is reused; older source-annotation/candidate-source
hashes are not treated as current evidence. Existing conditional typed
transport/lifetime results retain their actual premises. The old raw-resume
receiver-renaming bridge, wildcard bypass and type-equality-as-grant shortcuts
are not reused.

## Mutual TODOs, omissions, and stop

`CB-PERMISSION-REVIEW-1`: Luna assigns fresh independent review of these exact
bytes and dependencies, adjudicates the obstruction, and selects the next
contract seam. Producer/coauthor is ineligible to certify it.

`CB-PERMISSION-TRANSPORT-1`: provisional runtime implementation evidence request,
owned by Luna at program/receiving/machine. Required inputs: approved annotation
policy, this exact source/consumer trace and fresh review. Proposed output:
source-authenticated callback Result entry/receipt/view/event/owner transport
through `OperationResultConsumer`, preserving family-specific local grant and
unknown inherited coverage. Exact falsifiers: a sibling invocation or view can
grant `q`; the permission ends before the consumer emits `q`; foreign owner or
type equality supplies authority; signal permission handles `write`; annotation
alone invents inflow or removes unrelated residual. A new source owner/write
lease requires Luna's versioned amendment. This TODO grants no current code write.

Omitted: arbitrary callbacks/aliases/structural paths, wildcard/scoped release,
computation-form thunk, polymorphic operation instances, source acceptance,
full static residual proof, F1/FK1, general source/native correspondence,
FIRST-RESULT-ADEQUACY, soundness/principality, VM/native equivalence and actual
execution. Tests, builds, probes, Git and independent review were not run.

Resources: 1200 active seconds granted. First instrumented work timestamp
`2026-10-23 23:45:43 UTC`; proof freeze observation
`2026-10-23 23:50:15 UTC` (272 seconds through proof freeze). Handoff finalization
is included in the final elapsed receipt sent to Luna. Eighty read-only shell
calls through the dependency recheck; one final SHA receipt call remains at
creation of this inbox. Three apply_patch calls total create/update only the
two leased Markdown files. Zero tests/builds/runtime probes/heavy processes,
Git operations, descendants or external contacts. CPU/memory totals UNKNOWN.

All new paths are exactly the proof artifact above and this inbox; no scratch
paths or extra outputs. **STOPPED after final hash receipt; writing ceased,
both outputs frozen, no running shell sessions or descendant leases.** No
in-envelope producer stage remains after the exact obstruction stop condition.
This is an unreviewed research checkpoint pending Luna's review/integration,
not parent closure. The inbox's own revision-1 byte hash is sent out of band
to avoid a self-referential hash.
