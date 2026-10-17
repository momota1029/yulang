# NPAIR SWR1 typed Local supplier prototype

Sprint: `npair-swr1-output-origin-prototype-20261018`, rev3, contract SHA-256 `b8d32df7ed62c5b62c5c8671e2979801024f83a9bc3ed83e92802532f7c45d08`.
Assignment: `/root/npair_native_demand_children`, implementation lease, baseline `77bc688cb587a73559ba1e8d37234e739a9f8848`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; OPEN, closure 0.

## Result

Added a private, non-admitting `LocalSupplierCandidate` record to the candidate-call source owner and a source-side constructor at the existing Local/CatchBinder callee guard. The candidate binds the exact owner, Apply index and occurrence, original callee index, ordered Group/Ascription/Block-final wrapper path, terminal Local index/occurrence/source key/`HirLocalId`, unique binding and slot, initializer index/endpoint, and action positions.

Construction requires one owner-matching Local binding and slot; one exact unannotated `Action::Install` for its initializer; one exact `Action::Local` for the terminal occurrence; and `Install < Local < Apply`. A matching recursive `Action::Link`, `LocalAnnotation`, CatchBinder, duplicate join, mismatched owner/endpoint, or missing action produces no candidate. The existing scoped Apply guard still returns `unavailable()` immediately. Candidate runtime status is explicitly `PendingGuard`: no ApplySourceInput, LocalUse, FreshUse, source_call, relation, or runtime join is produced by the refused scoped input.

The helper retains a candidate in the source Plan before the pre-existing refusal; collection aborts, so this Plan data is not externally observable. This is structural prototype code, not a successful runtime supplier join. It does not relax admission or change source semantics. No CatchBinder generalization, SWR1 membership, complete Sigma, fixed-c, Replay, or parent-theorem claim is made.

## Review, execution and dependencies

The frozen proof artifact `notes/theory/2026-10-18-npair-swr1-output-origin.md` SHA-256 `f401f3f1dbd389af3643658c42aa90f3367a51d259ecb367075337c8eba252af`, handoff SHA-256 `6db042e2cc84e20538ea63431de30d6a9d3262ef9ae55c4c9e8d0dc6202a38df`, received a fresh CLEAN proof review. That review supports the five static identity joins and valid-state Missing/remap lemma, but explicitly does not certify this prototype or dynamic runtime join. A fresh compiler review of the exact frozen code bytes found a MAJOR resource-accounting defect: wrapper traversal uses infallible `Vec::push`, repeated scans are uncharged, and candidate storage is absent from Plan accounting. This blocks executable integration. The compiler reviewer found the identity joins and refusal behavior structurally explicit, but Capture/FreshUse remaps remain unestablished. The reviewer STOPPED without tests or writes.

No Cargo, build, test, or probe was run in this sprint. The earlier exit-2 result belongs to the predecessor diagnostic sprint, not this prototype. No command was started because only 125 seconds remained at the latest receipt, insufficient for final independent review plus a 120-second bounded run.

Frozen prototype SHA-256 (preserved in the review receipt; these code bytes were not integrated and have been restored from the reviewed baseline):
- `candidate_source.rs`: `a25ab55401e67b503bda678cf9cc0e5d50b400ac5131d6005b5487002956a483`
- `candidate_call.rs`: `22733799641b9eb19a976e4fff1419f628a4cb54b9bcab5e43f7b4fc483c823b`
- Fixture `tasks/agent-loop/fixtures/20261017-receive-choose.yu`: restored baseline `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`

Direct source pins used: HIR LocalSource `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`; candidate_scope `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`. Proof review is limited to the proof artifact and baseline/source premises, not the modified code.

## Remaining exact boundary

The scoped guard executes before `ApplySourceInput` creation and before solver `LocalUse`/`FreshUse` construction. Therefore the target fixture cannot provide a dynamic join while that guard is preserved. The unreviewed-for-integration prototype has been reverted from executable source; the committed baseline hashes are `candidate_source.rs` `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b` and `candidate_call.rs` `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359`. A successor implementation must make traversal fallible, charge/bound its work, and account for retained storage before considering runtime attachment. Any admission change remains gated by proof, exact Local/FreshUse identity and remap checks. Runtime supplier attachment and all dynamic remap observations remain UNOBSERVED.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. Actual start: 2026-10-17 21:16:10 UTC. Last measured receipt: 2026-10-17 21:24:05 UTC, elapsed 475s, remaining 125s of the 600s implementation cap. No descendants or disposable scratch paths. Writer STOPPED after freezing this note and its inbox handoff.
