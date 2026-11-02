# Sprint R260 — source-wide ReplayChildAck order at R70

Status: ADMITTED under the unchanged full goal: Yulang inference soundness and its Rust implementation. Preserve the original accepted source domain, parent theorem, Simple-sub A/B and quantifiers. This packet targets one existing terminal-edge premise; no parent or production closure is assumed.

## Fixed outcome

R259 was independently reviewed PASS for one initialized ordinary exact-HIR drain through authentic Diagnostics, Acknowledgements, ReturnReady and frame removal, applying SUFFIX250. It does not prove the global successful-forward premise that the replay acknowledgements at every reached Diagnostics cut are valid and ordered for their original Replay operations.

Prove a constructor/transfer-wide ownership and order invariant for every consuming `ReplayChildAck` on the existing initialized successful-forward domain. Start from all source constructors of acknowledged replay children and all queue/frame transfer sites. Preserve each raw operation ID, child index, cursor and parent frame. Establish that asynchronous replay children enter a frame in increasing operation-index order; front-inserted structural work, rewritten/aliased children and source-set union do not mint or duplicate consuming rights. Treat synchronous restoration, nested typed frames, partial queue transfer, Running/Ready delivery, successful commit, frame removal and retained acknowledgements explicitly. Show that a later child for an operation cannot complete in a nested frame while an earlier child remains pending outside it.

Apply the resulting invariant at every actually reached Diagnostics cut in the existing successful-forward domain. Combine it with R249's independently reviewed unconsumed-owner/operation/child-index/cursor retention and R250's independently reviewed SUFFIX250, only under their exact premises. The proposed parent application discharges the **ordered-authoritative-ack premise** of the existing R70 terminal edge. Keep diagnostic-reference validity/origin/fiber, successful helper premises, actual eventual Diagnostics entry, evidence authenticity, and every other R70 premise explicit and open unless separately proved.

Success is a source-constructor/transfer proof applied at the unchanged R70 edge, or one actual accepted-prefix counterexample identifying the first ownership/order violation. A FIFO proof for one flat queue, the R259 example, a numeric index inequality without nested-frame ownership, or an unqualified source sketch is not success. Do not narrow source forms, graph modes, A/B, quantifiers or semantics; do not infer a production defect or whole-language parent closure.

Implementation lane: Luna/high, **NO_SAFE_CODE_SLICE**. No production edit absent a concrete accepted-source violation of an approved clause.

## Assignment, leases, inputs and limits

One registered `prover`, Sol/high, proposed identity `/root/sol_r260_replay_ack_order`, no descendants; maximum 2,400 active seconds across at most three substantive stages. Exact write leases:

- `notes/theory/2026-11-02-replay-ack-order-r260.md`
- `tasks/agent-loop/inbox/replay-ack-order-r260.md`

Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git.

Baseline HEAD: `cb00f3329cd02b0049a88467945b118d1c2dec75`. Inherit the 36 direct source pins from `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256 `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`; all revalidated MATCH at admission. Independently reviewed inputs:

- R249 contract `tasks/agent-loop/sprints/prior-replay-owner-lifetime-r249.md`, `3a1d10f09a84dc3fc35621ee0c202672009349dadf2d386b00c06a49028757b5`
- R249 theory `notes/theory/2026-11-02-prior-replay-owner-lifetime-r249.md`, `615121840e60fe86b493a3e9b9236783770cc8bbd002cea6c4e41b29d60e90e9`
- R249 handoff `tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md`, `381d7d65f8de903611e9896fc56498a4ce005b551c08d073b63e9c891657a246`
- R249 reviewed history `tasks/agent-loop/history/20261102-r249-admission.md`, `484f939f5c212e54c0efef3ab5c3496c9058be02669db1c1ab71e91757f4f95d`
- R250 contract `tasks/agent-loop/sprints/ordinary-drain-progress-r250.md`, `9772cca143817a6d2a5a803334f5b5047b9846154a57b3cd95be67cb5c837c7a`
- R250 theory `notes/theory/2026-11-02-ordinary-drain-progress-r250.md`, `87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574`
- R250 handoff `tasks/agent-loop/inbox/ordinary-drain-progress-r250.md`, `8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65`
- R250 reviewed history `tasks/agent-loop/history/20261102-r250-admission.md`, `b1e3b90b118474f2704f668cb14bcad350b5579dd0c114d31fda16f77403c2ad`
- R259 reviewed outcome `tasks/agent-loop/history/20261102-r259-admission.md`, `940ea216758abd2721fb3d595d5258249e1553142314f7560fffad91a93db947`

Critical owners are already in the inherited manifest: `candidate_context.rs` replay/restoration/frame lifecycle and acknowledgement state; `lib.rs` queue, typed frame, terminal and commit phases; extrusion restoration and ack construction; scheme local/module FreshUse; effect direct-item creation. R249 supplies storage lifetime only under its reviewed successful-history premises. R250 SUFFIX250 remains conditional on valid diagnostic references and acknowledgements. No new source dependency is admitted. If proving a constructor/transfer case requires another owner, stop and return that exact dependency to Luna for admission.

After the primary-owned assignment checkpoint moves HEAD, record its administrative-only movement and revalidate all 36 direct hashes before Sol reads. Luna owns central state and Git. Requested and observed model/effort remain separate; missing runtime metadata is UNKNOWN. Freeze both outputs and stop all writes before independent review.
