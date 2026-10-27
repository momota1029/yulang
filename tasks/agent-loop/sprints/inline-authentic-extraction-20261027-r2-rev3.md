# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — revision 3: freeze extractor code before execution

Status: admitted by Luna as a versioned same-sprint continuation. The full
original type-inference/executor goal, source domain, quantifiers, meanings and
parent gates remain unchanged. This revision admits extractor source authoring
only; execution is held behind a further immutable revision.

## Exact accepted graph and baselines

This revision inherits all non-resource terms from the frozen r2 contract
`inline-authentic-extraction-20261027-r2.md` (SHA-256
`af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`) and its
lock-reconciliation revision 2 (SHA-256
`710fb4436e87ecd8575c6f01b9cd0109e098939275c3f0c4b9c5445b7db9fe9c`).

- Source baseline: `232b024e0d793714027170a388ab746ce0d2b429`, with its pinned
  source-owner/Lean hashes unchanged.
- Implementation resume checkout: `c6265fbf28d9dc408d89205d6f58aaaddaea3214`.
- Reconciled checkout after the scheduler receipt: `0d34874bce755ddf0be5a83fbad0a230d75ad848`.
- Luna's independent lock/graph verification:
  `inline-authentic-extraction-20261027-r2-lock-verification.md`, SHA-256
  `2291d919faaa300e1370f0f7b4e98a23f7bf0b9a2a5d10bcc26388441e37dac7`.
- Frozen dependency inputs: isolated manifest SHA-256
  `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; isolated
  lock SHA-256 `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`;
  metadata graph SHA-256
  `595365e8f394504fcc5c04e638107158351e3731284877b5bb12044358778fb1`. All
  22 registry tuples match the pinned root lock; graph has 26 packages/nodes,
  one isolated workspace member, and no `yu-solver` package/node/edge.
- Accepted implementation handoff revision 2: SHA-256
  `6bbf5be439a268d63d38d990b5f073ce8021c6e5e0892610bd286b4028279031`.
- The current `src/main.rs` is only an empty target, SHA-256
  `536e506bb90914c243a12b397b9a998f85ae2cbd9ba02dfd03a9e155ca5ca0f4`.

## Implementation source/schema phase — no Cargo invocation

Resume the same registered `implementer` and the same exact leases:

- `tools/inline-authentic-extraction/src/main.rs`
- `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean`
  (generated output only; never hand-author it as if extracted)
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2-source.md`
  (handoff revision 3, sequential after Luna acknowledges revision 2)
- scratch only `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl`

Implement the provisional extractor using only the pinned package graph and
already existing APIs. Authenticate the same parse/HIR/source-root before
emission. Return the exact binder token range and check it equals the registered
parameter range. Preserve the raw Apply callee, actual argument, and each
explicit Group-to-inner projection separately. Serialize the outer-body form,
range and complete ordered incidence, retaining statement/final-expression
distinctions. Preserve actual parameter-resolution identities, nested
same-spelling shadowing and restored-sibling resolution; reject foreign parse
and HIR inputs before serialization. Do not introduce or imply a mapping to
original Nat Sites/Names/Context unless an existing owner establishes it.

After code and output schema are written, freeze the source handoff revision 3
with source code/schema hashes, direct pins, actual owners and the first missing
original allocation equation. Stop without invoking Cargo. Luna will inspect
the frozen code and schema; only a new immutable revision pinning those exact
hashes may authorize execution. If any dependency, manifest, lock or output
schema change is needed, stop and return it to Luna before writing outside the
leased source/handoff paths.

## Proof lane and execution gate

The registered `lean_prover` remains STOPPED on its exact r2 paths pending the
frozen source schema and then an executed trace. Do not hand-author a replacement
trace or check a theorem against candidate values. Once the actual trace is
frozen and Cargo has stopped, resume that same proof identity to validate byte
ranges, raw/projected incidence, full order, parameter resolution and the
nested-shadow/restoration facts. Apply `OriginalIdentityEntryOrigin` only where
the extracted values establish every premise; keep the original allocation and
universal refinement obligations explicit and OPEN unless actually proved.
Lean remains 4.35.0, at most 6 checker calls/360 aggregate seconds, with complete
source-cone hash, originating theorem types and transitive axiom audits.

## Preserved resource envelope and gates

R2 has used 4 of its 6 Cargo invocation allowance: two lock-generation attempts
and two metadata queries. At most **two** `cargo run --offline --locked`
compile/run calls remain, each no more than 120 seconds, one CPU and 1 GiB, one
verification owner, sequentially. The first can produce the authentic trace.
The second may be used only under a later revision if the first fails or a
reviewed repair requires a new source hash. No Cargo invocation is permitted in
this source/schema phase. No tests, installs, root manifest/lock changes,
compiler/HIR/parser/runtime/API/semantic changes or production work are granted.

The original 3600-second r2 active-work cap remains unchanged; stage active time
was not fully metered and is not refunded. Astra remains 0. All original A/B,
soundness, effect hygiene, principality, progress/termination, full Call,
source/native, whole-language, receipt/admission and production gates remain
OPEN. Fresh non-author review is still required after both lanes stop and the
final trace/proof application freezes.
