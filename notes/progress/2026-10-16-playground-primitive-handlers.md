# Playground direct primitive operation handlers

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Baseline: `ca4f77cf3` (runtime implementation base `f8c7a8a13`)
Status: bounded closed-program execution and actual visibility bridge complete;
full inference/runtime/production parents OPEN.

## Authority and implementation

The existing typed-boundary visibility disjunction permits a handler when its
actual event is unprotected or an authentic local Grant exists. The reviewed
[closed primitive theorem](../theory/2026-10-16-runtime-primitive-event-visibility.md)
constructively establishes the former for its whole closed source universe.
This checkpoint implements that certificate without a new language decision.

`runtime/primitive.rs` checks every retained definition, arm, dependency and
code occurrence with authentic binder/declaration IDs and separate Ground and
DirectCallee roles. Primitive Value argument/response ports and discarded
continuations are required. Lambdas, unknown/imported references, operation
aliases, nonprimitive/Computation ports, bound continuations and dependency
cycles withhold the certificate. Internal ground module dependencies and
admitted transparent ascriptions have explicit source preservation corollaries.

`RuntimeProgram::from_hir` computes one private immutable boolean only after
complete construction. Fresh `start` owns the closed initial context; the
current public API cannot inject another context or response. Certified code
cannot create a raw continuation. At handler selection the boolean supplies
only the negative side of visibility. Exact operation identity, active owner,
ordered shallow selection, payload compatibility and source OpCompat remain
required. The existing positive local Grant route is preserved.

Classification failure does not reject source or assert protection. This is
conservative provisional execution coverage, not a language restriction or a
certificate about arbitrary external contexts.

## Proof and independent review

Original source theorem reviewed by `runtime_semantic_review` at
`d8d3530fa8c1508ae7515d7a9fa1c1f1ee4d4738e3b8f43fcae92c19fb4e26d6`.
The same independent referee reviewed actual §6 at
`57880fee06f4f5f49f55600830101bb892269bbd1c2f1d4670e814494853fed5`, CLEAN.
Its constructor/consumer implication has no remaining assumed local bridge;
source well-typing and selected-arm compatibility remain explicit original
premises, not facts proved by the classifier or a successful test.

Mode M2, two reviewers: compiler-referee `runtime_semantic_review` for profile
production/context closure and actual proof; spec-auditor `runtime_contract_review`
for source scope, sibling behavior, tests and README. Both code reviews are
CLEAN. The narrow README delta is independently CLEAN. No repair round was
needed. Broader Function/B, general negative completeness, full runtime,
full source materialization, source inference and F5 replacement remain OPEN.
The later independently CLEAN [delimiter corollary](../theory/2026-10-16-initialization-outward-order-current-runtime.md)
§8 discharges the current-runtime pending-publication raw-capture branch by
unreachability; captured cache references remain supported. It selects no A/B
publication law or new global consumer.

Frozen implementation hashes (under `tools/inference-playground/`):

| Path | SHA-256 |
| --- | --- |
| src/runtime/primitive.rs | `ad0cfd8a8b7d7ad2a83a363668fbaf2bbf19764dceaf0f093978c342c1559ebb` |
| src/runtime/program.rs | `9bb9150a161fc0bed20fb4559649cf08719e570b0662558e9efadcf775edcc55` |
| src/runtime/machine.rs | `25e61fa3fd06bdf9da09750f37fcac321da9d28fbb27e650fd3cf37a604bd973` |
| src/runtime/mod.rs | `8707ad039dc402f2ff9e3ce243594e4524c838cfbfa5e6f4c877c51cd746f63e` |
| tests/runtime_primitive.rs | `2b6a99690e43442c9553786c420c7108bcc8d8d9974391b4f677b73572bac3db` |
| README.md | `acf3c0bfcaf40b1ff75e61ad81cb96a2fb159fa42c54382507a56f4232c35b43` |

## Verification and cost

Primary-owned serialized checks:

- `CARGO_BUILD_JOBS=2 timeout 180s cargo test -p yu-playground --test runtime_primitive -- --test-threads=2`: 6 passed; log `/tmp/yulang-runtime-primitive-focused.log`.
- `CARGO_BUILD_JOBS=2 timeout 300s cargo test -p yu-playground -- --test-threads=2`: all 90 tests passed, no warnings; log `/tmp/yulang-runtime-primitive-final.log`.
- Exact new README direct-handler stdin source with `CARGO_BUILD_JOBS=2 cargo run -q -p yu-playground -- --run main -`: exit 0, output `7`, 60-second cap.
- Owned-file rustfmt and `git diff --check` pass. No existing expectation was changed.

Two private classifier tests cover accepted and rejected universes. Six
integration tests cover direct selection, original arm/operation ordering,
normal returns, forwarding/shallow arm effects, whole-program exclusion,
positive-Grant preservation and runtime payload compatibility. The mismatch
control explicitly bypasses inference to exercise the runtime owner; other
positive examples use actual candidate inference.

Structural classification work/storage are linear in the code and dependency
edges, binders/arms and distinct signature operands, plus authentic-ID hash/
equality cost. It runs once; runtime adds one boolean check. Zero timing/RSS
measurements, benchmark samples or broad workspace suites. The full owning
package is the coherent phase check; record-only updates do not repeat it.

## Records and next work

README, `tasks/current.md`, `tasks/research-lab.md` and the design index are
synchronized in this checkpoint. The pending definition-materialization
question remains unstaged; no answer is assumed. Native first-Result adequacy
continues through the separately reviewed concrete source instance and actual
selected-use census. General negative/profile coverage and wider source-root
coverage require their original proofs and implementation handoffs.
