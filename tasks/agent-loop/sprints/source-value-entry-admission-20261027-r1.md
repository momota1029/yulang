# Sprint SOURCE-VALUE-ENTRY-ADMISSION-20261027/r1 — source receipt interpretation

Status: CANDIDATE until Luna pins this contract, records its hash and grants the exact leases below.
Branch / baseline: `yulang3` / `7a5c1c2436bfd364c2cfb545101eeb7ad4ec1f5a`.
Authority: user’s persistent full inference/executor goal; user’s explicit capacity-release instruction; [2026-10-08 contextual Function definition](../../../notes/design/2026-10-08-contextual-function-membership-definition.md) §§1–2; [Call semantic input realization](../../../notes/theory/2026-10-08-call-semantic-input-realization.md) §§2–4, 6; [original Call source-introduction contract](../../../notes/design/2026-10-07-original-call-source-introduction-contract.md) §§1–3; source constructors and receipt consumer named in the pins below.
Contract revision / SHA-256 / primary admission: r1 / pending / pending.

## Original outcome and success evidence

**Original parent:** full Yulang inference/executor correctness: original A/B claims, source quantifiers, scopes, supported source domain and shared witness remain unchanged. The selected source is the actual Value-entry formal receipt path for the current original Call/identity investigation. This packet advances one source/native admission premise only; it does not replace or narrow either parent theorem.

**Fixed outcome:** construct a faithful source receipt interpretation from the selected original Invoke/Receive source constructors, derive the existing scoped receipt admission and decode equations for that concrete interpretation, and apply the result to the existing `receipt_recovers_call` consumer. If an owning source constructor/readout law is absent, freeze the first exact missing law with its source owner, theorem type and required fields. Do not invent a permissive predicate, infer admission for arbitrary `LocalAdmissions`, or report the interface obstruction as a source counterexample.

Success requires one of:

1. A checked Lean constructor and theorem deriving the concrete `Admitted` and decode obligations from independently justified source fields, with theorem types and complete axiom audit; or
2. A frozen, source-owner-specific obstruction showing the first unavailable field equation, while preserving all open parents and a precise next owner.

The implementation lane supplies an independent read-only constructor-to-consumer trace from HIR through `RuntimeProgram::from_hir`, Closure/Apply/Delay and receipt timing. It supports exact source/native field alignment or `NO_SAFE_CODE_SLICE`; it does not authorize Rust edits. A useful result must identify which original premise it advances and avoid equating source receipt, pre-Force demand and post-Force callback receipt.

**Known premise boundary:** `LocalAdmissions.receipt` is independent and is left unchanged by the existing admission specialization. `OriginalFormalShared` creates a source receipt and `OriginalRecursivePair` records its source fields/order, but those are not asserted equal to the Rust Value-entry callback transition. The selected Call realization says actual Invoke establishes its receipt before designated Force; full semantic input realization remains open.

**Non-goals:** no weakening of original A/B, no `True`/desired-conclusion admission, no arbitrary-base admission theorem, no assumed simulation, no use of successful typing or future Return/callback as a receipt premise, no source restriction, no Rust/compiler/test edits, no production promotion, no root import. Soundness, Effect hygiene, principality, termination/progress, complete source/native correspondence and production remain OPEN.

## Two continuing lanes

### Proof — registered `lean_prover`

1. Extract the exact selected source Invoke/Receive receipt constructor and its independent premises; separate static receipt preconditions, receipt construction and later live authority.
2. Construct the faithful `ReceiptData` interpretation from source receipt, view, typed path, consumer, incidence, current event and parent path. Derive parent agreement, `Admitted` and decode only for that instance.
3. Apply the result to `OriginalIdentityRealization.receipt_recovers_call`; preserve source identity and the existing `OriginalCalleeDelayProvenance` prefix. If a required readout is not derivable, expose its exact owner and stop at that law.
4. Emit an originating-module declaration/type/axiom audit. Use Lean 4.35.0 from the pinned toolchain, one process, `-j1 -M1024`; no checker bypass and no hidden project axioms.

### Implementation — registered `implementer` (read-only)

Trace one source-origin path through `program.rs`, `machine.rs` and `receiving.rs`: HIR Lambda/Apply/Parameter identity, instruction/code labels, selected provider/Closure, invocation owner, Callee Delay/view allocation, formal receipt owner, pre-Force demand and post-Force callback receipt. Return exact field mappings and source locations, or owner-specific `NO_SAFE_CODE_SLICE`. Do not edit Rust or tests; do not repeat the already reviewed two-owner allocation audit except where needed to connect this source path.

Luna is the sole integrator. Freeze both outputs, then obtain fresh non-author review focused on source constructor authenticity, non-circular receipt fields, admission/decode and event order. Review runs only after all producer writes stop.

## Permissions, leases and resources

Baseline: `7a5c1c2436bfd364c2cfb545101eeb7ad4ec1f5a`. Current user explicitly released nine legacy capacity reservations after a live-roster check. Their worker states remain UNKNOWN and all historical paths remain quarantined; no new output may reuse them. No non-primary agent was live at sprint admission.

**Exact repository leases:**

- Primary: `tasks/agent-loop/current.json`; this contract; `tasks/agent-loop/sprints/source-value-entry-admission-20261027-r1-outcome.md`.
- Proof: `notes/theory/lean/YulangClosure/OriginalSourceValueEntryAdmission.lean`; `notes/theory/lean/AuditOriginalSourceValueEntryAdmission.lean`; `tasks/agent-loop/inbox/source-value-entry-admission-20261027.md`.
- Implementation audit: `tasks/agent-loop/inbox/source-value-entry-admission-20261027-source.md`.
- Fresh review, after producer STOP: `tasks/agent-loop/inbox/source-value-entry-admission-20261027-review.md`.
- Private proof outputs: `/tmp/yulang-source-value-entry-admission-20261027/proof`.
- No other path, directory or wildcard is leased. Do not edit frozen predecessor proofs or their handoffs.

**Resources:** 2700 active seconds total: proof 1200, implementation 360, primary 540, fresh review 420, dispatch 180. Proof: at most 6 checker calls and 360 aggregate checker seconds, one checker process. One heavy process maximum; no Cargo build/test is authorized. Astra 0. At most two producer assignments plus Luna; reserve two global slots for review/integration. Effective model/effort remain UNKNOWN until runtime receipt. Work may continue through related stages inside this fixed packet.

**Return to Luna before:** changing source meaning or domain; editing compiler/Rust/tests; adding or changing dependencies; changing any lease; relying on a new owner law or admission interpretation; exceeding wall/checker budget; or closing any parent/production gate.

**Stop conditions:** goal outcome above; exact unsupported source field law; authentic identity/event-order counterexample to this adapter; pin mismatch; unexpected active writer/path conflict; user STOP/session end; or resource boundary. Preserve UNKNOWN worker states on uncertain cessation. No temporary timeout releases a lease.

## Frozen dependency pins

Every listed byte must match at admission. Also enumerate and hash the complete imported Lean source cone in the proof handoff before checking; any additional imported module must be pinned before use.

| Source | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-07-original-call-source-introduction-contract.md` | `1dcdfc40990a93c52ced1ae3ee11fd393014634864da8c480f8f943a2065ebc0` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `notes/theory/lean/YulangClosure/OriginalRecursivePair.lean` | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` |
| `notes/theory/lean/YulangClosure/OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `notes/theory/lean/YulangClosure/OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `notes/theory/lean/YulangClosure/OriginalNameForceExtraction.lean` | `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531` |
| `notes/theory/lean/YulangClosure/OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `notes/theory/lean/YulangClosure/OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `notes/theory/lean/YulangClosure/OriginalValueEntryDemand.lean` | `9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63` |
| `notes/theory/lean/YulangClosure/OriginalCalleeDelayProvenance.lean` | `3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe` |
| `notes/theory/lean/AuditOriginalValueEntryDemand.lean` | `efceba608e3942710c4f53d8bfc1516ba3f18c5470b7fae64810e04020d04772` |
| `notes/theory/lean/AuditOriginalCalleeDelayProvenance.lean` | `18516d704c6d884505a59343083c023ed583c7213fb6ca858dfbf12c3c23eba6` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `tasks/agent-loop/history/20261027-user-capacity-release.md` | `7d30faa71449af50c50539307b3a11d062735b64d522eac93656467ff94968a8` |
| `tasks/agent-loop/inbox/callee-delay-provenance-20261027.md` | `aecc59dc6d88d255ef93706adaa44fad4de1f9a3a8029de56c64c68c987f3b4e` |
| `tasks/agent-loop/sprints/callee-delay-provenance-20261027-r1-outcome.md` | `a158f502b625a0bacbfa9b66a575d8758f78f75c2fe7f453872c7e830af8c345` |

The capacity-release rules and receipt are now committed at `7a5c1c243`; static state check passed before this sprint contract was created. Pin any modified version if the contract itself is later revised.

## Handoff and integration

The proof handoff records exact declarations and complete types/axioms, imported source-cone hashes, direct source correspondence, applied parent lemma or first open premise, check receipts, and author STOP. The implementation handoff records owner locations, field mapping/unavailable readouts, hashes and STOP. Luna freezes both handoffs before fresh review. The independent reviewer must assess the frozen bytes and challenge constructor provenance/circularity, event order, missing fields and the claimed parent application; conditional evidence stays conditional.

Luna updates compact `current.json`, records the outcome and hashes, stages only this contract and intended proof/implementation/review/outcome paths, inspects the full outbound range and pushes. No question bundles or pending-question paths are staged. Consult the dispatcher next at the first owner-law obstruction/counterexample, pin/authority/lease/resource change, frozen review seam, budget boundary or sprint END.
