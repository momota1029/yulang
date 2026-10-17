# Checked inlet bridge and entry control review — 2026-10-17

Sprint: `receive-checked-inlet-bridge-and-entry-control-20261017`, accounting contract rev5 (`acc6e476579a0819ae87d2e530a74c2b8c62c3d646d9c814f2ac06402098bca2`). Parent Goal remains active; original FORWARD-FIRST-CALL A/B and production gates remain OPEN.

## Adjudication

The source correspondence is accepted as a **bounded control-order result** for the selected returned `step` Value-entry path. Compiler review confirms the delimiter-relative suffix correction. Spec review is semantically CLEAN; its minor accounting finding is closed here by superseding the handoff's stale within-budget sentence with the controlling rev5 accounting below. Architect review is CLEAN. This receipt does not amend the handoff or reopen its source lease.

The four reviewed cases distinguish inner and outer handlers, each with and without a continuation. An inner handler catches before `ValueEntry` is popped; its suffix excludes that still-live frame, and its arm Return can bind the formal and enter the body. An outer handler is selected only after propagation crosses `ValueEntry`; a non-resuming arm abandons that invocation, while a captured suffix can restore it. Capture/abandonment includes `ValueEntry` iff unwind crosses the frame.

The revision-2 compiler MAJOR was repaired. Revision-3 delta findings (stale unconditional introduction and stale artifact hash) were corrected in revision 4. The subsequent compiler delta is CLEAN. No further edits were made after the source STOP.

## Frozen outputs and review receipts

- Control artifact: `notes/theory/2026-10-17-selected-value-entry-control-correspondence.md`, SHA-256 `78d8b06b8304a6c1556c569b4b4fb7d455aa172c3f7aa1902563068f756b4981`.
- Handoff revision 3: `tasks/agent-loop/inbox/20261017-selected-value-entry-control-correspondence.md`, SHA-256 `693ae61f61a1aef4e7c815a550a543d1171b71724f91b2dd274104efce8548ca`.
- Unchanged bridge candidate: `notes/design/2026-10-17-receive-checked-inlet-view-check-bridge.md`, SHA-256 `86c95b67c5dcb6fb03ed706838b6bde5da70639f53ba8594a85121821aa23ab5`.
- Unchanged bridge handoff: `tasks/agent-loop/inbox/20261017-receive-checked-inlet-view-check-bridge.md`, SHA-256 `f46ff320be6e018122c8e7dff149259bc6a4f4f1944f5920d4798b49e8c81a9d`.
- Compiler referee: revision-2 MAJOR; revision-3 delta MAJOR+MINOR; revision-4 delta CLEAN. All five runtime-source hashes match the artifact.
- Spec auditor: semantic CLEAN; minor stale handoff budget statement, superseded by this primary receipt. All 20 contract dependencies match.
- Architect: CLEAN within bounded scope; no new finding. Source ownership, candidate authority limits and `NO_SAFE_CODE_SLICE` remain intact.

## Resource and authority accounting

The source lane consumed **489 seconds against 480 authorized**, a **9-second overrun**. This violation is preserved; it is not reclassified or described as authorized. The author STOPPED and no source lease remains. Per selector adjudication, coordination allocation fell from 120 to **111 seconds**. Proof consumed 420/720 seconds; unused 300 retired. Reviews consumed 276 seconds (initial compiler 120, compiler deltas 10, spec 120 conservatively, architect 26). Reserve is 0. Charged total is **1185 seconds**; remaining planned review allowance is 204 seconds and coordination allowance is 111 seconds. The maximum accounting total is 1500, within the 1800-second envelope.

The bridge remains Draft/unselected. Both original F2 VIEW/CHECK inclusions remain OPEN at source-owned admission/domain correspondence and complete original guard occurrences. This result proves neither full typed-view simulation nor source `T`/native MODEL, arbitrary `c₂`, original A/B, or production readiness. No compiler edits, tests, builds, probes, runtime execution, semantic adoption or expected-output changes occurred.

Static tooling check passed: `python3 tools/agent_sprint.py check`. This check is not independent review or execution evidence.

**Adjudication:** REVIEWED-PARTIAL. Preserve the original quantifiers and continue the parent Goal through the next selector-routed sprint.
