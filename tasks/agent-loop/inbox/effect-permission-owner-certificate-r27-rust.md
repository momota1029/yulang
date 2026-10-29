# Effect permission owner certificate R27 Rust repair handoff

## Frozen receipt

- Source repair froze: 2026-10-29 21:30:52 UTC.
- Active time: 372/400 seconds; no process launched.
- This is a source-only revision. No Cargo, rustc, build, test, formatter, runtime, Lean/Lake, or checker was run.
- Candidate JSON was not created. The source and mutation behavior remain unverified until fresh exact-hash review and later authorized execution.
- Reviewer result for the prior revision: REJECT. The immutable prior sources and full review are preserved at `tasks/agent-loop/history/effect-permission-owner-certificate-20261030-r27-rust-preflight-r1/`, commit `640942a64`.

## Final source hashes

- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/machine.rs`
  SHA-256 `c75a719580a032959693713f67db6ab73f7a8a0440855c409db6cbd94aa2566a`
- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/receiving.rs`
  SHA-256 `7a8eeab787f127064d5689b1ee5fbbfc409b4a307905d0f42d538f5d3d628f25` (unchanged)

The worker confirmed both starting hashes matched the rejected frozen revision. Only these two leased Rust files were edited.

## Source delta

1. The callback test selects `answer` through `definition_named`; the companion continues to select `main`. The approved source texts and expected results remain `1` and `23`.
2. Replay evidence is joined to the selected request and consumer using the actual OwnerReturn stack index/tag, event-specific pre-unwind pop transitions, stored suffix coordinates, and owner restoration. A global set of previously seen template handles no longer stands in for this causal link.
3. The full relevant pop chain is recorded separately from the captured template suffix and retained outer stack, before forwarding consumes and moves boundaries into the request suffix.
4. The observation-only `capture_root_index` lookup is gated with `cfg(test)`.
5. Guarded mutations were added for an unrelated replay, a wrong request event, and deletion of the actual pre-unwind replay boundary. Each checks that its target exists and changes before requiring rejection.

The author reports these additional observations fit schema r2 without changing existing field meaning. This is not yet independently reviewed. If review finds the existing schema cannot represent the causal evidence faithfully, stop for a Luna schema decision.

## Remaining gates

Fresh independent exact-hash review is pending. Candidate compile and focused runtime remain gated on that limited ACCEPT and separate Luna stage authorization. If authorized later, the remaining R27 source/runtime budget is 328 seconds; keep the existing allocation ceilings: compile 120, one focused invocation 120, evidence/handoff 60. Reserve at least 400 of the reviewer's 870 remaining seconds for the generated certificate and mutation outcomes. Lean remains unchecked with zero budget; combined R27 and all parent/production gates remain OPEN.
