# Amendment 01 — pin the restoration child writer

Sprint: `NATIVE-COMPLETED-EMISSION-READBACK/r3`
Base contract SHA-256: `d1c194c85c54d7ea2016c64e60d51d7805e480ae7c824b167f0bc86fee94d71e`
Authority: Luna, following a bounded `next_action_selector` recommendation.

## Reason and exact source addition

The proof lane followed the already pinned call chain to the mutable
`settle_candidate_intrusion` call in `lib.rs:14311`. The implementation of that
child completion writer is outside the base pin set. The proof lane stopped
before reading or searching its body and froze the boundary in handoff r1:

`tasks/agent-loop/inbox/native-completed-emission-readback-r3-proof.md`
SHA-256 `c71c79cc623bbaa95247925ce4bfc5f780578caf736c53c7e1a619fa12cc3ccd`.

Add this exact read-only dependency:

- `crates/yu-solver/src/candidate_intrusion.rs`
- SHA-256 `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`

Authorized read scope is limited to `settle_candidate_intrusion` and callees
defined in this same file that determine its state writes, through the first
actual physical write site for the referenced admission/emission rows,
relation/flow/transformer, or addressed bound slot. Record the exact write
branch, condition, referenced identity and preservation argument. Do not read
another unpinned file body. If this path reaches another unpinned owner, stop at
the first call boundary and return its owner and first unresolved writer.

## Assignment and limits

The proof worker may resume only after ACKing this amendment hash before reading
the added source. This adds no write path, output, worker, child assignment,
check, build, theorem claim, or semantic authority. It does not change the
original theorem, existing evidence, review-before-check gate, or production
status. Rust implementation continues under the base contract unchanged.

The proof worker has at least 847 seconds remaining in its original 1,000-second
grant according to the first observed clock window; no renewal is granted. The
amendment source investigation is capped at 300 seconds within that remaining
grant. If this is insufficient, stop and report the exact remaining boundary.
No Lean/Lake/build/check/test execution is permitted before the fresh source
review accepts the frozen R3 artifacts.

All R1/R2 deviations and incomplete dispositions remain unchanged. The original
parent, source domain, quantifiers, effect policy and all production gates remain
OPEN.
