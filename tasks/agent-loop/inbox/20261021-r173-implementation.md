# R173 Luna implementation packet — revision 4 review target

Sprint `source-drain-attribution-and-consumer-join-20261021-r173`, contract
revision 3, SHA-256
`13660d1a7044ae995f5e326fd610d0d83afa517dc9f31d699b8a1be4288a2b80`. This sequential handoff preserves
the candidate identity frozen in revision 3 and assigns it to one fresh
independent final review. It authorizes no probe.

## Identity and result

Proof baseline remains commit `7ec64a3788175913a2be46331cf0f64c6bd5b407`.
Activation metadata remains `9547edfc7`. Proof rev1 is STOPPED and baseline-only;
it does not certify any implementation candidate. The unchanged fixture is
`tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

R173 implementation author: Luna primary `/root`, observed model/effort
UNKNOWN/UNKNOWN. The R173 rev2 delta reviewer was `/root/r173_rev2_delta_review`;
its CLEAN receipt covers only the reviewed rev2 delta. The aggregate 720-second
independent-review allocation is charged in full because elapsed runtime is
UNKNOWN. Luna explicitly reallocated the former 300-second conditional probe
allocation to one fresh final candidate review; the probe is revoked and remains
NOT_RUN. Candidate-specific proof remains OPEN; no probe, build, test, evaluator
or Yulang2 execution was performed.

## Frozen implementation candidate

```text
c005b99c1aa6da3c6b203e19c37f8b99700618815528f33d67cbf70941df78f5  crates/yu-solver/src/lib.rs
723cc253090ad2b4a0c67a1a17c57bc0587b26e4dc4d90a642f45ab0d1f468fa  crates/yu-solver/src/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  crates/yu-solver/src/candidate_scheme.rs
7a4c64d3783496029225be043ea8914543ceff1841caed5fcec19d68dcfb4932  crates/yu-solver/src/shadow_apply.rs
d1652f573dff08336b1e6b4b46faa18d5ab3e38e0e8980402e5e686d74c8c172  tools/inference-playground/examples/r173_source_drain_attribution.rs
7dfc4b5b186f5056e4f12420f6d62ddaacad1855f715181afab64507898f50ce  notes/theory/2026-10-21-r173-source-drain-attribution.md
```

The earlier rev2 manifest remains preserved in the contract and prior handoff
history; neither it nor proof rev1 certifies these bytes.

## Construction and current limits

The typed drain receipt is attached to the exact Origin only after successful
enqueue. The Origin copy retains task, CauseId, incoming relation, Replay ack,
created/selected relation and Origin/drain indices. It is initially incomplete;
the terminal drain path marks it complete before the frame is removed. The
source query reads completed receipts from retained Origins after solve, and
keeps incomplete/missing receipts unavailable. Transaction rollback truncates
newly created Origins; source solver decisions do not read this passive record.

The query emits source facts and receipts, direct-seed dependency rows,
same-graph provider routes, typed Capture bounds/snapshots, typed FreshUse map
entries (including empty-map markers), and forwarding Apply consumer relation
rows. Completeness flags fail closed on truncation, unavailable attribution,
missing routes/maps or non-unique consumer relation.

This does not prove the universal forwarding theorem or establish candidate
behavior. The exact final review must still challenge receipt lifecycle and
rollback, source-task authentication, same-provider Capture/maps, and whether
the consumer relation's membership in the provider's captured bounds is
justified. No inference probe is authorized from this handoff. If a future exact
review does not establish an attainable discriminator, record NOT_RUN and the
first missing owner.

## Worktree and integration

Only the six R173 implementation paths above plus this handoff were written by
Luna in this continuation. Existing unrelated dirty R152–R163 artifacts remain
untouched. Static `git diff --check` passed. No tests or builds were run.
Candidate-specific proof remains OPEN. The fresh final review is assigned
against this handoff revision and the exact manifest above. Probe and
integration remain unauthorized pending review and broader parent gates; only
Luna may stage or commit eligible exact paths.
