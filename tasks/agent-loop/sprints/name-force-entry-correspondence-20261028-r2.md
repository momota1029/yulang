# Sprint NAME-FORCE-ENTRY-CORRESPONDENCE-20261028/r2

Status: READY for live assignment; research only
Branch / baseline: `yulang3` / `224f5aafc7ff88dc5f17016dbb24b59e9799c543`
Authority: unchanged original source/soundness obligations in `notes/theory/2026-10-08-call-semantic-input-realization.md` §§4.1–4.3; current proof boundaries in `notes/progress/2026-10-27-name-force-extraction-review.md` and `notes/theory/2026-10-27-original-name-force-extraction.md` §5.
Contract revision: r2; primary Luna `/root`; semantic policy unchanged.

Delta from r1: after the source handoff showed that Cargo 2 compiled the library but stopped in the binary conversions, permit exactly one additional `cargo run --locked --bin name_entry_trace` (Cargo 2→3 total, ≤120s, one CPU, 1GiB) solely to produce the missing actual trace. No tests, direct-binary fallback, fourth Cargo call, new fixture/dependency/output lease, or semantics change. Before that command, source owner must relabel the current misleading `entry_site` field as the returned value origin (or provide the actual ValueEntry locator from its owner), freeze the exact binary/dependency hash, and await Luna’s hash confirmation. Preserve r1 handoff and both failed receipts; write handoff revision 2. The bounded command must write only the already leased trace outputs. Total/source/proof/review budgets do not increase; source owner reported r1 wall use below 1000s, leaving room for the 120s cap.

## Original outcome and success evidence

Advance the original ValueEntry/receiver correspondence by constructing the existing `OriginalIdentityCarrier.EntryFacts` packet for the dictionary-free lexical Name/Observe constructor from its actual post-Force observation. Preserve the original demand, compatible-future, surrounding-world, capture, inertness and semantic premises. The proof must use one computed observation event for its snapshot, observation, raw return, parent/node lookup and bind inputs. It must not identify that post-Force event with the earlier receipt event; `EventProof` logical eta/witness adjustments stay explicit.

Success: a checked conditional constructor theorem derives `EntryFacts.executed` and `actualReturn` from `OriginalNameForceExtraction.allocated_bound_force`, `return_receipt`, and `OriginalReturnWorld.computed_return_event`, then applies the existing entry/identity consumer. A source trace records one actual invocation joining Name observation → `consume(Observe)` receipt → ValueEntry parameter binding, with matching event, owner, value/view and before/after cell counts. Fresh review accepts the frozen theorem types/axioms and trace correspondence. The scoped remaining premise is materially narrower only if the same-event packet is actually constructed; otherwise report the exact first obstructing field.

Unchanged parent domain: inert formation and every actual finite observation at every independent compatible demand, including arbitrary other carriers. This Name case is a subclaim. Complete Call, other carriers, all A/B claims, whole-language soundness, effect hygiene, principality, termination and production remain OPEN.

Non-goals: no semantic change, source-domain restriction, receipt-based permission, changed tests/expectations, claim that dictionary poststate is unchanged, assumption of successful Force/Return/bind, root-context decision, or production/cutover authority.

## Continuing lanes and exact leases

Proof (`lean_prover`, Luna/high requested): own `notes/theory/lean/YulangClosure/OriginalNameEntryCorrespondence.lean` and `tasks/agent-loop/inbox/name-entry-correspondence-20261028-proof.md`. Read the pinned source modules below plus the governing obligation. Keep all external semantic and independent-demand premises explicit; apply the constructed packet to the existing consumer. One verifier/cache owner; ≤10 Lean/Lake calls and ≤600 seconds total; no root import edit and no project-wide default build.

Source (`implementer`, Luna/high requested): own `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/runtime/receiving.rs`, `tools/inference-playground/src/runtime/mod.rs`, new `tools/inference-playground/src/bin/name_entry_trace.rs`, `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean`, and `tasks/agent-loop/inbox/name-entry-correspondence-20261028-source.md`. Instrumentation is bounded, reversible and research-only; preserve runtime behavior. The leased trace binary uses a minimal inline source fixture through the ordinary `RuntimeProgram::from_hir`/`execution_roots`/`start` driver. No fixture/test/expectation edits or new dependencies. Maximum three Cargo commands (r2 grants only the single command above), runtime ≤1000 seconds, one process, 1 CPU, 1 GiB RSS target; tests=0. Source lane does not write the correspondence theorem.

Reviewer (`compiler_referee`, fresh non-author, read only): frozen source trace and correspondence theorem; falsify event mismatch, receipt/value/view/owner mismatch, binding based on earlier receipt snapshot, or hidden dictionary poststate treated as unchanged. Require complete theorem types, transitive axiom audit, actual source call order and exact scope limits. ≤600 seconds, ≤1 verifier, tests=0.

Proof scratch: `/tmp/yulang-name-entry-correspondence-20261028/proof/`; source scratch: `/tmp/yulang-name-entry-correspondence-20261028/source/`. No overlap with prior quarantined leases. Only primary owns current.json, shared parent files, staging and Git.

## Frozen inputs (SHA-256 at admission)

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalNameForceExtraction.lean` | `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531` |
| `notes/theory/lean/YulangClosure/OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `notes/theory/lean/YulangClosure/OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `notes/theory/lean/YulangClosure.lean` | `3c38da4bb2e017249fa973e0ee28f243d44ba6d52b6f173ac617b605f1fce9e8` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `tools/inference-playground/src/runtime/mod.rs` | `4c7981d775bbbed0ead2f1bac742f772581bc41be91fba7d05f7946fa889c992` |
| `tools/inference-playground/src/bin/inline_authentic_extraction.rs` | `1ab6f3ed86d6bfc6d8f73baa40e5e46d5e3d451922af06fc1092a93ca29a39c0` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |

Workers must hash-check assigned direct dependencies before editing. A mismatch, missing source owner, semantic decision, overlapping lease or resource breach returns to Luna. Do not edit the frozen inputs listed above unless they are explicitly listed as output paths (none are).

## Resources, stop and integration

Total fresh sprint envelope: 3600 seconds: proof 1600, source 1000, review 600, Luna integration/verification 300, dispatch 100; at most six assignments, one verifier at a time, ≤1 CPU/1 GiB per heavy process, Lean ≤10 calls/600s, Cargo ≤3 total (r2 grants one additional invocation ≤120s), tests 0, Astra 0. Actual model/effort and session/receipt are recorded only from tool evidence; unknown stays UNKNOWN. No worker recursively spawns.

Stop on goal, exact obstruction, authority/dependency/lease mismatch, resource limit, or user STOP. Freeze one handoff per lane with hashes, checks, limits and writer-stop status. Keep all parent gates OPEN until their original scope is discharged and independently reviewed. Update current state and durable outcome; checkpoint only a coherent reviewed or explicitly unreviewed research-only milestone. Luna stages explicit paths, inspects the full outbound range, and pushes non-forced only when coherent.
