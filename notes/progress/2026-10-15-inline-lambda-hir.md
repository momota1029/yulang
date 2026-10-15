# Inline lambda private HIR formation

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Baseline: `0ac1c96e7`
Status: private HIR formation and original source-correspondence proof complete, independently reviewed

## Authority and bounded construction

After the completed unary-lambda parser checkpoint, the primary identified
anonymous-lambda HIR connection as the next stage. The user's direct reply
`お願いします．` authorizes that continuation, including the necessary compatible
source-provenance representation. This is an implementation checkpoint under
the existing language contracts, not a replacement language design.

Governing sources are the Authoritative
[unary parser](../design/2026-10-15-unary-lambda-parser.md) §§3–4,
[native source-Generalize definition](../design/2026-10-08-source-generalize-definition.md)
and its selected source rules, and
[inference top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md).
The existing named-formal contract in
[F5 foundation](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md)
§§3–4/21 supplies ordinary spelling-based binding, including `_`. Catch's
explicit wildcard interpretation is a separate context. Contextual words in
the body keep the ordinary expression grammar; lowering does not reinterpret
keyword constructs as parameter references.

The private `LocalSource` builder will retain genuine LambdaExpression nodes
using its existing Lambda form, root-owned parameter namespace and lexical
work stack. Each literal allocates one parameter, installs it while forming
the body, and restores the prior lexical depth. Captures retain their original
identities; no synthetic named group, local binding or generalization boundary
is introduced. Existing constructor-directed allocation order is retained,
without a new global source-order promise.

The source sidecar will distinguish authentic IdentifierPattern origins from
inline Lambda origins with an exact direct-Identifier token range. A checked
typed accessor exposes both. The existing `parameter_source_position` keeps
its IdentifierPattern-only contract and returns `MissingSource` for inline
origins. Anonymous parameters receive no fabricated named-local owner.

Recovery-bearing or unsupported source continues to fail private formation
with `StructuralProjection`; failed construction publishes no successful
carrier. Ordinary `ResolvedExpr` lowering and runtime migration are outside
this gate. The Authoritative
[callback-context delivery](../design/2026-10-03-callback-context-delivery.md)
contract remains binding and its literal/consumer correspondence remains OPEN.

## Proof, review and verification budget

The stable parent obligation quantifies over every successful private
formation of supported enclosing source with unary literals: fresh root-owned
parameters, nearest lexical resolution and original captures, exact lexical
restoration, authentic lambda/binder/body provenance, and failure without
fabricated successful publication. The proof producer first derives the
existing work-stack invariant, then must bridge the actual new constructor.
A conditional derivation alone does not close this parent gate.

Mode M2. Architecture and binder-source audits have supplied the construction
packet. Closure requires independent compiler-referee review of construction
and proof, and specification review of provenance compatibility and scope;
no unresolved accepted blocking/major finding. One batched repair follows
adjudication of the assigned reviews. Delta reviews remain in their dependency
cones. Primary owns all integration and Cargo execution.

Verification budget: focused HIR lambda tests and existing source-identity/
local-source sibling controls, bounded playground source controls and two
existing solver consumer controls, then one playground package check. Cargo uses
two build jobs, bounded timeouts and one test thread. No workspace-wide suite,
benchmark or timing experiment is selected; measurement budget is zero.

## Completed implementation, proof and review

The architect found two production source owners: `module/local_source.rs`
and `shadow.rs`. The binder audit established reuse of the current generic
identifier-formal contract. No additional user decision is needed for that
reuse. The implementation retains a literal directly, shares the named-local
parameter allocator, brackets body work with lexical restoration, and exposes
`ParameterSourceOrigin` through `parameter_source_origin`. Existing named
parameter access remains compatible. Production edits are confined to those
two owners; HIR and playground integration tests occupy separate new files.

The [formation theorem](../theory/2026-10-15-inline-lambda-hir-formation.md)
first derived the existing stack invariant, then discharged its original
C1–C5 premises at the actual constructor and provenance consumer. Fresh
compiler-referee review found one reversed word in the CatchArm scheduling
description; the producer corrected it to save Restore before installing
binders, matching the unchanged source. Independent textual delta review
closed that finding. There are no remaining construction/proof findings.
The original supported source domain and all identifier spellings are retained.
ShadowArtifact availability remains its existing independent preflight; body
provenance retains ordinary HIR granularity and the authentic raw OperatorChain,
without inventing another HIR occurrence.

The specification auditor found no production conformance issue. One new test
incorrectly equated Integer node text with its significant token spelling.
The actual literal emission retains its leading space inside IntegerLiteral,
and the existing HIR stores complete node text. Prewrite specification review
approved comparing the retained string with its exact original source slice
and independently checking the original Integer token `1`. No existing
expectation or production representation changed. The final test delta and
five playground tests also passed independent specification review.

The primary applied the independently reviewed theorem to the frozen two-file
implementation and checked all 12 dependency records before final record
synchronization (11 source/design files plus the dispatch receipt). The receipt
status was subsequently synchronized here; its construction section remains
the original input. This closes the private HIR formation parent gate. It is
not a proof of inference, principal types, callback elaboration or execution.

## Verification and resource accounting

All Cargo commands used `CARGO_BUILD_JOBS=2 timeout 180s`; tests additionally
used `-- --test-threads=1` (and `--exact` for the two named solver controls).
Primary was the sole Cargo owner; commands were serialized.

| Command | Final result |
| --- | --- |
| `cargo test -q -p yu-hir --features shadow --test inline_lambda_local_source` | 6 passed |
| `cargo test -q -p yu-hir --features shadow --lib source_identity_correspondence` | 6 passed |
| `cargo test -q -p yu-hir --features shadow --test conditional_local_source --test catch_local_source` | 14 passed |
| `cargo test -q -p yu-playground --test inline_lambda` | 5 passed |
| `cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_annotated_function_formals called_and_unused_callbacks_check_actual_providers` | 1 passed |
| `cargo test -q -p yu-solver --features shadow-apply-candidate --test simple_sub_local_source_retirement different_initializers_and_nested_renamed_blocks_retain_integer_results` | 1 passed |
| `cargo check -q -p yu-playground` | passed, no warnings |
| `git diff --check` and scoped new-file whitespace checks | passed |

Final total: 33 focused tests passed. The initial six-test run and a diagnostic
rerun failed only the new raw-literal assertion described above. No production
repair was needed. The package check ran once; no unchanged broad suite was
repeated after test/comment/record updates. No full workspace, runtime backend,
benchmark or performance measurement ran (zero timing samples). Added work is
one parameter allocation and registry entry per literal, direct header/trivia
inspection and an on-demand direct-child origin lookup; no solver graph pass
or new constraint is introduced.

Four positive playground source controls now reach existing candidate
inference: a named binding initialized by a literal, direct literal application,
a local literal initializer, and a literal passed to `int -> int`. An
incompatible Unit-result literal produces the existing type conflict and
withholds graph exports. These are end-to-end executable observations, not a
general callback-context theorem.

## Remaining gate and integration

The exact next callback obligation belongs to `candidate_source.rs`: its
`Work::Visit` currently carries expression/level/region, and Apply visits the
argument before the completed Apply relation. Establish how the actual
source-use instantiated callback interface and original slot/profile reach
the literal before its first body constraint, as required by callback-context
§§2–2.1. Current ordinary Function compatibility does not supply that bridge.
Pure/Handler context delivery, full inference proof, ordinary HIR cutover,
imports/loops/std and runtime remain OPEN.

Primary synchronized `tasks/current.md`, `tasks/research-lab.md`, the design
index and the proof's adjudication status. The parser question directory was
excluded from this implementation checkpoint; the user subsequently requested
its separate historical archive. No documentation or record sync is
silently deferred. The coherent change is integrated on the recorded research
branch after explicit-path staging and outbound-range inspection.
