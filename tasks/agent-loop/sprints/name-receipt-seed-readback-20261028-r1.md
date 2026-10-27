# Sprint NAME-RECEIPT-SEED-READBACK-20261028/r1

Status: READY; fresh paired source and constructive Lean packet. Fresh ceiling **1800 seconds**. Baseline: branch `yulang3`, commit `a011fdde6`. Prior Name-entry outcomes, including the MAJOR stale-Local coverage correction and the later frozen-output overwrite, remain immutable and unchanged. The overwritten historical scratch bytes remain lost/quarantined; every output in this packet uses a new path with exclusive create semantics.

## Fixed outcome

Construct the actual native receipt seed from the accepted direct Name/Name invocation and derive its five `ReturnAlignment` fields from their owning constructors, then apply them immediately to `OriginalNameEntryCorrespondence.constructed_name_realization`. A new wrapper that assumes the seed, the same-event equality, or any ReturnAlignment field is not closure. If any field cannot be derived, freeze the exact missing equation and its source owner; do not weaken the theorem or claim parent closure.

The Lean lane starts from `OriginalIdentityRealization.Use` and the exact `ReturnAlignment` fields:

1. `fiber`: receipt-seed assignment-event fiber equals the post-Force event fiber.
2. `eta0`: the same assignment's eta0 is preserved.
3. `views`: source view assignment equals the event's views.
4. `shared`: the assignment's shared witness equals the post-Force shared witness.
5. `readback`: `OriginalReturnWorld.fields` over the actual saved frames, assignment and Return packet equals `eventFields` of the post-Force event.

Use `OriginalNameForceExtraction.eventAt` only with its actual construction: it preserves fiber, eta0, views and shared witness relative to its demand event. Derive the connection between that demand event and the receipt seed from the actual preparation path; never identify them by name or by equal handles. Derive Return readback from `OriginalReturnWorld.fields` and the actual readout. Preserve the existing `EventProof` permission for logical eta/witness changes. Apply the constructed result to `constructed_name_realization`; retain its full theorem type and axiom audit.

The source lane exposes structured raw inputs for the accepted direct case: actual invocation/callee/formal identity, carrier/Delay incidence, receipt, saved parent environment, cell/view readbacks, and the post-Force snapshot consumed by ValueEntry. Mark every output field as represented by native execution, externally supplied, or unavailable. Raw handles alone establish no semantic assignments or witnesses. Only add bounded read-only observation/accessor code; no runtime decision or compiler semantics may change.

## Exact leases and frozen dependency cone

### Source lane writable paths

- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/receiving.rs`
- `tools/inference-playground/src/runtime/mod.rs`
- New driver `tools/inference-playground/src/bin/name_receipt_seed.rs`
- New generated data `notes/theory/lean/YulangClosure/OriginalNameReceiptSeedTrace.lean`
- New handoff `tasks/agent-loop/inbox/name-receipt-seed-20261028-source.md`
- New source scratch `/tmp/yulang-name-receipt-seed-20261028/source/`

### Proof lane writable paths

- New Lean module `notes/theory/lean/YulangClosure/OriginalNameReceiptSeed.lean`
- New handoff `tasks/agent-loop/inbox/name-receipt-seed-20261028-proof.md`
- New proof scratch `/tmp/yulang-name-receipt-seed-20261028/proof/`

The source and proof writers own disjoint files. The proof lane may map the constructor chain and develop only equations derivable from the pinned owning definitions while source tracing proceeds. It must not import or assume unverified generated data; final integration and the one pinned Lean verification occur after the source lane freezes the generated trace and hash. The reviewer starts after both lanes freeze and acknowledge cessation.

All other files are read-only. In particular, existing theorem modules and previous traces/handoffs are frozen. No tests, fixture/expected-output edits, dependency changes, new assumptions/axioms, `sorry`, `admit`, semantic decision, source-domain widening, nested sprint, or output overwrite. Every new output path must use create-new semantics and abort if it exists. Before any write, verify that all admitted new outputs are absent.

### Pinned source and proof dependencies

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/runtime/machine.rs` | `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `OriginalNameForceExtraction.lean` | `10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531` |
| `OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `OriginalNameEntryCorrespondence.lean` | `3b362e91b66ae106259875bc49644545f1f107ed644c74393791fc2dca2a0f20` |
| `OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Any mismatch stops the affected lane before edits/builds. Record the exact hash gate in both handoffs.

## Resources and gates

Fresh ceiling **1800 seconds**: constructive Lean proof900, source500, Luna100, fresh independent review250, dispatcher50. No transfer, inherited allowance, retry or renewal. The source lane may make exactly one locked Cargo invocation, at most 120 seconds, one CPU and 1 GiB RSS target. The proof lane may make at most 8 Lean/Lake calls, at most 300 seconds total, under the pinned Lean 4.35.0 environment, with complete theorem type and transitive axiom audit for every new theorem. At most one project verifier call. Tests=0, Astra=0. Record actual UTC starts/stops and every command/resource result; UNKNOWN stays UNKNOWN.

Source and proof lanes may begin in parallel after separate ACKs and their own hash/path-absence gates. Their outputs remain separated; proof integration awaits exact source-output hashes. Any shared dependency write, source change, unavailable observation, timeout, unprovable field or resource limit stops the affected work and records the earliest obstruction. No optimistic completion, budget transfer or renewal.

## Fresh independent review

Fresh non-author reviewer, identity distinct from every earlier Name-entry reviewer and either source/proof author; read-only ≤250 seconds after both lane cessation ACKs. Inspect the frozen generated trace, source accessors, all new Lean bytes, original theorem types, full axiom audits, and the actual constructor-to-readout chain. Check that no field was assumed, reconstructed from handles alone, taken from another call, or joined to a post-Force event without proving its connection to the receipt demand. Any failed join, hidden external premise, axiom/`sorry`, false resource receipt, output-path reuse, or scope deviation leaves outcome INCOMPLETE. Reviewer runs no Git, Cargo, tests, or Lean.

The prior frozen-output overwrite and reviewer read-only Git deviation remain recorded in `NAME-ENTRY-SEQUENCE-20261028/r1`; this new sprint's new outputs cannot repair or replace the lost prior bytes. All parent/A-B, full Call, effect hygiene, principality, termination and production gates remain OPEN unless the original complete obligation is actually discharged and independently accepted.
