# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — revision 6: final locked run

Status: Luna-authorized continuation after the repair-only rev5 stop. The fixed
r2 outcome and original inference/executor goal, source domain, quantifiers,
semantics and all parent gates remain unchanged. This revision authorizes one
final execution, Cargo invocation 6/6, of the repaired provisional extractor.

## Frozen inputs

Inherited contracts: r2 original SHA-256
`af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`, rev2
`710fb4436e87ecd8575c6f01b9cd0109e098939275c3f0c4b9c5445b7db9fe9c`, rev3
`3f81bb6399ba732ca8bf3843ec4a9e43617dd4349946230e2930d65099e422e`, rev4
`1e99d83d65fd89705a4ce28db5da111b3d1e0fa4055faba1513b7bb8ec65ba0f`, and
repair-only rev5 `fa07dfb5670d093497e1caeeefa915acef4c554f98d569fd8e5ae558edf7f948`.
The rev4 call-5 failure is preserved in
`tasks/agent-loop/history/20261027-r2-cargo-call5-failure.md`, SHA-256
`88fc68ea768da69a3f849ecbd616e72d69878c1730ebf6d48c67908b29a9754f`; it
remains consumed and is not replaced by this attempt.

- Parent source baseline: `232b024e0d793714027170a388ab746ce0d2b429`.
- Execution checkout: `78abf9fb7b7016aefe8568e64db4d1c3ae52418d`.
- Repaired `tools/inline-authentic-extraction/src/main.rs` SHA-256
  `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`.
- Implementation handoff rev4 SHA-256
  `6bd6117267cee513880b5b596935e9c0763bd061ba33024251a858417cd1158a`.
- Isolated `Cargo.toml` SHA-256
  `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`;
  `Cargo.lock` SHA-256
  `2ee467b8f6416aa7dda36f96f3401a0b0ae24a739ff7c6a2efccc1323777ee91`.
- Offline locked metadata graph SHA-256
  `595365e8f394504fcc5c04e638107158351e3731284877b5bb12044358778fb1`.
- The current trace output
  `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean`
  is absent. It may be created only by the authorized command below.

Luna independently inspected the rev5 diff: only the leased extractor and
sequential implementation handoff changed. Three reported source-position
fields now map the exact selected-artifact `Position` reference to its table
index; the unrelated parent-child ordinal is not used. The seven diagnosed HIR
availability failures retain fatal propagation and operation-specific error
context. Owner pins and all manifest/lock/graph pins match. This review is
static; the repaired source has not yet compiled or run.

## Exact implementation lease and one command

Resume the same implementer identity `/root/inline_authentic_extraction_impl_r2`.
Before execution, recheck every frozen input above and confirm no trace already
exists. Write command/environment/stdout/stderr/exit-time receipts only under
`/tmp/yulang-inline-authentic-extraction-20261027-r2/impl` using new `run-r5.*`
names. Reuse the retained `target-r4` cache. Run exactly this command from the
repository root, with the full invocation, environment and redirections stored
verbatim as `run-r5.command.txt`:

```sh
/usr/bin/time -f 'ELAPSED_SECONDS=%e EXIT=%x' -o /tmp/yulang-inline-authentic-extraction-20261027-r2/impl/run-r5.time timeout 120s taskset -c 0 env CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_DEV_INCREMENTAL=false CARGO_TARGET_DIR=/tmp/yulang-inline-authentic-extraction-20261027-r2/impl/target-r4 RUSTFLAGS='-C debuginfo=0' bash -c 'ulimit -v 1048576; exec cargo run --offline --locked --jobs 1 --manifest-path tools/inline-authentic-extraction/Cargo.toml' > /tmp/yulang-inline-authentic-extraction-20261027-r2/impl/run-r5.stdout 2> /tmp/yulang-inline-authentic-extraction-20261027-r2/impl/run-r5.stderr
```

Limits are one CPU (CPU 0), 1 GiB virtual memory, one Cargo process, and 120
seconds wall time. Do not run a second command, retry, compile separately, run
tests, update dependencies, invoke Lean/Lake, or change source/schema. No seventh
Cargo invocation exists.

If the command succeeds, first confirm extractor completion and process
cessation, then freeze the actual generated trace hash and append implementation
handoff revision 5 with all execution receipt hashes and exact invocation
outcome. Stop immediately after handoff. If it fails, preserve the raw receipts,
confirm trace absent or partial and process cessation, append the failure
handoff, and stop. Do not repair or retry inside this revision.

## Proof gate and preserved scope

The same proof identity remains STOPPED until a successful run, Cargo
cessation, and Luna acknowledgment of the exact source/handoff/trace hashes. On
success it may consume only that generated trace under its inherited limit of
at most six Lean checker calls and 360 seconds. It must return actual theorem
types and complete transitive axiom audits; a finite trace establishes neither
Rust behavior by itself nor a universal frontend law. No hand-authored trace or
invented original-coordinate allocation is admissible.

R2 remains capped at 3600 active seconds with no reset; prior unmeasured time is
UNKNOWN. Cargo use becomes 6/6 on this attempt whether it succeeds or fails;
the prior call 5 failure remains charged. Astra remains 0. No compiler/HIR/
parser/runtime/API, semantic, test or production changes are authorized. Fresh
non-author review remains required after both lanes freeze their handoffs.
Original Site/Name/declaration/root-Context/ambient allocation, universal
frontend refinement, all A/B, soundness, effect hygiene, principality,
termination, source/native, whole-language, receipt/admission and production
gates remain OPEN.
