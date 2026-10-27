# Sprint NAME-RECEIPT-SEED-READBACK-20261028/r2

Status: READY after separate worker ACKs. Fresh ceiling **2400 seconds**. Baseline: committed `yulang3` HEAD `de22b32793a1cf4ef71d5e68de45b8c2a25d23c3`. All writes occur in the isolated clone `/tmp/yulang-name-receipt-seed-isolated-20261028`, on branch `research/name-receipt-seed-isolated-20261028-r2`, rooted at this baseline. The primary worktree's modified `machine.rs` and `receiving.rs` remain UNKNOWN-owner QUARANTINED and are not read, copied, or modified by either lane.

## Fixed outcome

Find the first source-backed bridge from an actual direct Name/Name invocation through receipt creation and Force to the ValueEntry operands, and discharge the corresponding actual `OriginalNameReceiptSeed` readback obligations in Lean. Success requires an actual trace from the pinned source constructors, all derivable fields proved without assumed equalities, and application to `constructed_name_realization`. If the source does not represent a semantic assignment/witness or a required equation is absent, report the earliest exact constructor/equation and owner; this is a valid discriminating INCOMPLETE outcome, not parent closure.

The source lane must trace the Closure Callee arm, formal/environment, invocation, Delay incidence, receipt, Force and exact post-Force ValueEntry operands. Classify every output field as native-represented, externally supplied, or unavailable; handles alone establish no assignment or witness. Only bounded read-only observation/accessor changes are allowed. No runtime decision or compiler semantics may change.

The proof lane must first elaborate and audit the 11 declarations in the frozen r1 `OriginalNameReceiptSeed.lean`, then derive the common decoded root preparation from the actual receipt/demand path and derive `ReturnAlignment` (`fiber`, `eta0`, `views`, `shared`, `readback`) from their owning definitions and observed source equations. Apply the result directly to `OriginalNameEntryCorrespondence.constructed_name_realization`. No guessed assignment, assumed equality, name-based event identification, new axiom, `sorry`, or weakening the parent theorem. Preserve the full theorem type and transitive axiom audit for each new theorem. A failed source join or unprovable field stops at its earliest obstruction.

## Exact isolated leases

Paths below are exact paths inside the isolated clone; no equivalent path in the primary worktree is leased.

### Source lane

- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/mod.rs`
- New `tools/inference-playground/src/bin/name_receipt_seed.rs`
- New `notes/theory/lean/YulangClosure/OriginalNameReceiptSeedTrace.lean`
- New `tasks/agent-loop/inbox/name-receipt-seed-20261028-r2-source.md`
- New `/tmp/yulang-name-receipt-seed-isolated-20261028/source/`

### Proof lane

- `notes/theory/lean/YulangClosure/OriginalNameReceiptSeed.lean` (isolated copy of frozen r1 candidate; no primary-worktree edit)
- New `notes/theory/lean/YulangClosure/OriginalNameReceiptSeedRealization.lean`
- New `tasks/agent-loop/inbox/name-receipt-seed-20261028-r2-proof.md`
- New `/tmp/yulang-name-receipt-seed-isolated-20261028/proof/`

Source and proof writers own disjoint files. All other paths are read-only. The source lane may not import or assume generated trace data from the proof lane. Proof integration and pinned verification wait until the source trace and handoff are frozen and hash-pinned. Fresh review begins only after both writers freeze and acknowledge cessation. Every new output must use create-new semantics and abort if present; verify all new output paths absent before first write. No tests, expected-output/fixture changes, dependency changes, semantics decision, source-domain widening, nested sprint, or output overwrite.

## Pinned dependencies

The following SHA-256 values must match in the isolated clone before edits/builds. Any mismatch stops the affected lane.

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/runtime/machine.rs` | `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `OriginalNameReceiptSeed.lean` (frozen r1 input) | `14a5fc3d69c827ba246942353b1adec22316461b51068fd82e1861494b5f0d9a` |
| `OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `OriginalNameForceExtraction.lean` | `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531` |
| `OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `OriginalNameEntryCorrespondence.lean` | `3b362e91b66ae106259875bc49644545f1f107ed644c74393791fc2dca2a0f20` |
| `OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## Resources, gates and review

Fresh ceiling **2400s**: proof 1100s, source 650s, fresh independent review 400s, Luna 200s, dispatcher 50s. No transfer or renewal. Source: at most 2 Cargo invocations/240s total, one CPU, 1 GiB RSS target. Proof: at most 8 Lean/Lake calls/360s total under pinned Lean 4.35.0, at most one project verifier call, full theorem types and transitive axiom audits. Tests=0; Astra=0. Record actual UTC start/stop, commands, resource results and UNKNOWN observations. Each lane starts only after its own ACK and hash/path-absence gates.

Fresh non-author reviewer, distinct from all prior Name-entry reviewers and both authors, read-only ≤400s after cessation ACKs. Inspect exact frozen bytes and hashes, source constructor-to-readout chain, every new theorem's full type and axiom audit, output provenance, and parent application. No Git, Cargo, tests or Lean by reviewer. Any unproven join, hidden external premise, false resource receipt, reused output, or scope deviation yields INCOMPLETE. The r1 outcome remains immutable. All parent/A-B, whole effect-hygiene, principality, termination, implementation and production gates remain OPEN unless the original complete obligation is actually discharged and independently accepted.
