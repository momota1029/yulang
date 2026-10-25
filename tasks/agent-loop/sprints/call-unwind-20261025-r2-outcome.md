# Call request/failure initial-prefix typing r2 outcome

**ACCEPTED / CLEAN within the exact r2 scope.** Luna's composition compiled and
the fresh nonauthor combined review found no BLOCKING, major, or minor issues.

Contract: `call-unwind-20261025-r2.md`, SHA-256
`4847f89672c8821df47d9ed2e1162b150b3b578b4aec8304e6d2331389c27c01`.
Baseline: `33cd9e0a5`; branch `research/simple-sub-intrusion`.

## Accepted result

The unchanged raw P/Q unwind theorems and both initial-trace corollaries are
accepted for the frozen formal `CallControlStep` relation. The corollaries
start from an actual initial Call state, require an independently typed
literal suffix and a supplied finite prefix to the exact requesting/failing
head, then append the actual frame unwind. Their length is exactly
`n + (s.frames.length + 1)`. Request capture preserves innermost-first
nesting, `captureBind` response-index lifting, effect/result expose order,
existential world/scope results, and final `viewContext = observed`. Failure
uses `md.failWorld_total` through the exact context-frame mapping and all four
actual cleanup constructors, keeps the final world existential, and preserves
only the endpoint fields stated in the theorem.

The r1 composition failed because its proof did not carry the initial
`resultType` and literal-suffix equalities through state destruction. R1 was
stopped exactly at that failure; its source and receipt remain frozen and
unaccepted. R2 uses a distinct source that normalizes those two equalities
before destructing the state. It does not import the failed r1 composition.

## Verification and review

The 62 frozen source/evidence/output pins all matched on revalidation. Their
canonical digest is
`0474c62d41565f73a40a375ab97f73ca2f94a34783acfe751f44a33d0ea4ad91`.
Exactly two serialized Lean invocations ran, composition then signature/axiom
query. Both used `lake env lean -j1 -M1024`, timeout 120 seconds, exit 0, no
timeout and empty stderr. Complete argv, timestamps, streams, input hashes and
outputs are recorded in `inbox/20261025-call-unwind-r2-verification.jsonl`,
SHA-256
`581819ffc547cd47d4885c6cecceffa372ce41603c707825bb3f5a529b87267b`.

The exact query reports no axiom dependencies for raw request unwind, raw
failure unwind, or prefix append. Each initial-trace corollary depends only on
`[propext]`, within the accepted finite-typing dependency boundary. The
query-source SHA-256 is
`77a685433f4815977207ee32a5ba9cf49d707a993e43a29c169cb12954f0df0b`; its
complete stdout SHA-256 is
`a54b68f9e54eb717ee2ce2d385cf5138e052c848633da0a8f6cb5f9937aebffb`.

Fresh combined review: `inbox/20261025-call-unwind-r2-review.md`, SHA-256
`e3391a49968f668eb106daccaa47979d4165a313525d0d1f2827784c012ee079`.
The reviewer independently checked the exact propositions, constructor/frame
coverage, capture order and binder, cleanup witnesses, metadata/world
boundaries, prefix length, signatures, axioms, all 62 pins, and full streams.

Composition source `CallUnwindTypingRepair.lean` SHA-256:
`1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3`.
Its `.olean` and `.ilean` hashes are respectively
`8467499d9a4a00bb8afbfcadd9e9dd08866b26c0614a9743d80eda85cef4cb84` and
`20becfc8e8705b3446f042e3d85ea580dd5e55192ab8305937944b7934b7c257`.

## Boundaries

This result does not establish that a requesting or failing state is reached,
global progress, successor coverage, external resumption, metadata meaning,
cleanup correctness, lifecycle restoration, source/native correspondence,
ordinary-Control handoff, original Call A/B, inference A/B, or production
closure. The viewed-delay gap and r9 remain OPEN/UNACCEPTED. No Rust/runtime
implementation was performed. These parent obligations remain open for the
next dispatcher decision.
