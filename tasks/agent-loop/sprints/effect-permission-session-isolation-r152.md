# R152 — isolate permission registration to its owning session

Status: admitted continuation under the unchanged user goal. This packet
addresses one reviewed identity-boundary regression in an unpushed research
diff. It does not close source/native, INITIAL-STATE, CONSUMER, A/B, or
production gates.

## Frozen input and authority

Committed source baseline: `225c5519943fc490c3d5620683918674f4f6afd5`.
The exact three-file research input is
`tasks/agent-loop/inbox/effect-permission-session-isolation-r152-input.patch`,
SHA-256 `643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a`.
It is a frozen copy of the existing dirty diff for exactly `candidate_effect.rs`,
`candidate_scheme.rs`, and `shadow_apply.rs`; it is not applied. Baseline blob
hashes: `candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`,
`candidate_scheme.rs` `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`,
`shadow_apply.rs` `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`.
Relevant design: annotation integration `a95e048e...`; inference principles
`7701841a...`; design authority `e4055100...`.

Dirty working-tree files are not worker inputs. Read committed baseline blobs
and the frozen input patch only. `candidate_receiver.rs` and quarantined runtime
files are explicitly excluded. Do not force `provider == source owner` for
returned/local functions; authenticate their actual construction owner.

## Fixed outcome and exact leases

Proof/source lane: registered `prover`, 600 seconds, exact output
`tasks/agent-loop/inbox/effect-permission-session-isolation-r152-proof.md`.
Show that the session-owned route, state, registrations and FreshUse mapping
come from one actual InferenceSession, or identify the missing owner evidence.
Falsifier: two sessions from the same source have equal IDs/ordinals yet can be
joined into one permission-use record.

Implementation lane: registered `implementer`, 900 seconds, exact outputs
`tasks/agent-loop/inbox/effect-permission-session-isolation-r152.patch` and
`tasks/agent-loop/inbox/effect-permission-session-isolation-r152-source.md`.
Reconstruct a candidate against committed blobs plus the frozen input patch.
Prefer the original session-owned wrapper; any alternative must use an
unforgeable common owner/brand and explicitly reject cross-session joins.
Audit every changed non-test API and removed source/native check. If no coherent
nonempty supported diff remains, report NO_PATCH. Output stays unapplied and
uncompiled.

Fresh independent `compiler_referee`, 360 seconds, reviews the entire candidate,
all exact base/caller paths, owner/permission provenance and failure publication.
Primary integration: 180 seconds. Total ceiling: 2040 seconds. Builds, tests,
Lean execution, new cache/environment, scratch, checkout/worktree: zero.

## Stop and promotion boundary

The review must cover the complete proposed candidate, not only the binder
repair. Preserve rollback, permission origin, captured raw/canonical rows,
provider/arm distinctions and all valid owner cases. A reviewed patch may be
checkpointed only as an unapplied research artifact. It does not authorize
production integration or establish source-wide hygiene. If any deleted check
or new cross-session path remains unjustified, HOLD the whole candidate and
return the exact evidence needed to repair it.
