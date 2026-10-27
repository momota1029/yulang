# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r5

Status: ADMITTED — one-owner outer checkpoint correspondence for r2 B
Baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`
Parent: unchanged full inference/executor soundness and original permission
endpoint-image obligation. Preserve source domain, accepted semantics, A/B
claims, quantifiers and source/native scope.

## Fixed outcome

Establish or refute the first missing equation from r4 using the newly admitted
`candidate_intrusion.rs` owner and the already admitted source-owner union:

1. For the same candidate state and route, `State::begin` captures
   `effect_algebra.checkpoint()` before permission/domain publication.
2. Publication journals each new formal-domain key in that same undo consumed
   by rollback; active-undo absence or replacement cannot silently skip this.
3. `State::rollback` passes that checkpoint to effect-algebra rollback and
   restores the associated row/term epoch before another capture/export can
   observe an invalid retained association.
4. Commit retains the originating permission/domain and live terms; abort
   removes the new association before retired offsets can be reused.

Inspect candidate-state identity/replacement, preexisting associations, and
capture-artifact survival. A correct checkpoint equation alone does not close
all of r2 B. Keep r2 C (canonicalization/store association) and D (successful
capture/export) separate. An actual counterexample must show a reachable
originating construction, a stale/mismatched association surviving abort, and
successful capture/export of an endpoint outside the original captured image.
Offset reuse, stale lookup alone, missing-root unavailability, or a local
checkpoint fact is insufficient. If another owner is needed, state its exact
path/equation and stop without opening it.

## Authority, source pins and output

Primary owns authority, this contract, current state, adjudication, review and
Git. One read-only `researcher` may inspect only this previously admitted
owner union:

| Owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Frozen r4 contract: `d158c2e14e44d6f6c5bc3e76af7a1ec94cf24c090ba266de9ad93ce958b0b1cc`;
r4 handoff: `92fc0eb406ad0b7b82801ed86c33723bdc9483aee997421563dac2d12154d8a7`;
r4 independent review: `1511ef47588a0b754743c812c7c77ef2b75c9dbe1b5d746bace031f9b8c7e757`.
Retain r2/r3 evidence and r1's unchecked Lean blocker; no theorem promotion or
implementation authority follows from this packet.

Exact output lease: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r5.md`.
No Rust edits, Cargo, Lean/Lake, tests, probes, network, Git, or descendants.
Do not touch quarantined paths. Hash mismatch or resource bound ends the packet.

## Runtime and review

- Role: registered `researcher`; no descendants.
- Budget: at most 200 seconds, one CPU, 1 GiB RSS; no renewal.
- Report exact state identity, checkpoint ownership, publication journal path,
  commit/abort disposition and any unresolved owner/premise with source
  locations and hashes. Keep all parent, theorem, native and production gates
  OPEN.
- Freeze the handoff and assign a fresh non-author `compiler_referee` before
  any Lean bridge or proof promotion.
