# Sprint R261 — diagnostic-child references at reached Diagnostics cuts

Status: ADMITTED under the unchanged full goal: Yulang inference soundness and its Rust implementation. Preserve the full accepted source domain, original parent theorem, Simple-sub A/B and quantifiers. This packet targets only SUFFIX250's diagnostic-reference premise; it does not prove eventual Diagnostics or full soundness.

## Fixed outcome

R260 was independently reviewed PASS for ORDER260: at every actually reached Diagnostics cut in the inherited initialized successful-forward domain, consuming ReplayChildAck rights are ordered by their original operations under the reviewed R249 retention premises. Applying R250 SUFFIX250 still requires valid diagnostic references: every recorded child must have an actual memo at the reached cut, with Pending children admitted to the delta and external children Complete.

Prove a constructor/consumer invariant for those diagnostic-child references. Inventory every actual producer: aliases, newly retained rewrites, all structural forms, ordinary replay, and settlement reopening/merge replay. Classify inactive/fallback paths explicitly. Follow actual Context-consumed work, memo shortcuts, delta admission and child completion; an enqueue alone does not establish a memo or child processing.

Give special attention to `candidate_replay_bound`, which records a diagnostic edge before replay enumeration. For every actually reachable producer case, prove either that its canonical input fibers produce the required child and eventual memo, or that frontier/dependency suppression retains a previously emitted real child for the same diagnostic owner and that child's processing is Complete/Pending in the exact state consumed by SUFFIX250. Cover scoped BoundTransport, FreshUse/restoration, copied bounds, source qualification, and merge canonicalization where their constructors reach this path. Keep raw and canonical BoundKeys, source origin, transported fiber and child identity distinct; diagnostic origin metadata is not a substitute for the missing origin-to-fiber relation.

Apply the reference invariant with ORDER260 at actually reached Diagnostics cuts. Discharge only the diagnostic-reference premise for constructors whose source/consumer chain is established. Keep successful-helper premises and actual eventual Diagnostics entry explicit and open. If the first failure belongs to R71 or origin-to-fiber authenticity, freeze the exact first constructor, raw/canonical keys and missing association for a new admitted packet rather than assuming it away.

Success is the source-constructor proof applied at SUFFIX250 under its unchanged remaining premises, or one accepted-prefix counterexample identifying the first unadmitted diagnostic child. A flat “every enqueue is memoized” claim, the R259 owner-emission route alone, or narrowed source scope is not success. No source-wide progress/termination, production defect or full parent closure follows automatically. W, R71/evidence, F1/FK1, foreign continuations and other soundness premises remain separate.

Implementation lane: Luna/high, **NO_SAFE_CODE_SLICE**. No production edit absent a concrete accepted-source violation of an approved clause.

## Assignment, leases, inputs and limits

One registered `prover`, Sol/high, proposed identity `/root/sol_r261_diagnostic_reference_closure`, no descendants; maximum 2,400 active seconds across at most three substantive stages. Exact write leases:

- `notes/theory/2026-11-02-diagnostic-reference-closure-r261.md`
- `tasks/agent-loop/inbox/diagnostic-reference-closure-r261.md`

Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git.

Baseline HEAD: `d7e886e6d1dd9a3a3318908a8425937b3ca7703d`. Inherit 36 exact direct source pins from `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256 `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`; all revalidated MATCH at admission. Frozen R260 reviewed inputs:

- contract `tasks/agent-loop/sprints/replay-ack-order-r260.md`, `741296c13bb3af9d46580c2340f377c9da8a42dd680b2df5098a1b13ecc381cb`
- theory `notes/theory/2026-11-02-replay-ack-order-r260.md`, `87455f756a26d7d4cab0368be3e3b67741c7afe70d958407cc3de2cde90a1aca`
- handoff `tasks/agent-loop/inbox/replay-ack-order-r260.md`, `af45ee4039f81997a96e5df51bb2fe5a32c1c52b53c02359aae51316d1a77f94`
- reviewed outcome `tasks/agent-loop/history/20261102-r260-admission.md`, `92158dbd774f794eb6eb1225b219ca07d747ab389a979481f041fa392e39a06d`

R260 authenticates nine R249/R250/R259 reviewed inputs transitively through its frozen contract/theory. Critical owners remain in the admitted manifest: `lib.rs` diagnostic edge creation, memo/delta/consumer and typed phases; extrusion replay; context attachment, Context discharge, fiber/frontier and canonicalization; effect bound admission; scheme FreshUse; intrusion merge/reopening. No new dependency is admitted. If a reached source form requires another owner, stop and return that exact dependency to Luna.

After the primary-owned assignment checkpoint moves HEAD, record the administrative-only movement and revalidate all 36 direct hashes before Sol reads. Luna owns central state and Git. Requested and observed model/effort remain distinct; absent runtime metadata is UNKNOWN. Freeze both outputs and stop all writes before independent review.
