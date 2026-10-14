# Normal-return Catch and the native residual primitive

Date: 2026-10-14
Branch: `research/simple-sub-intrusion`
Baseline: `21d5a9773e577bf9b49b5d978bc60bedf8d72a42`
Status: normal-return source/playground slice complete; operation-handler and hygiene gates OPEN
Mode: M2; two implementation reviewers, separate bounded proof review; zero measurements

## Authority and executable change

The user requested continued effects/handler implementation through a playground,
proofs and repairs. The [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
and [intrusion charter §§14–15](../design/2026-09-29-scc-intrusion-redesign-charter.md)
govern source constraints and shallow Catch behavior. Existing Catch CST and
frozen Oracle normal-value lowering supply this slice's behavior. No new
handler semantics or parser contract is adopted here.

LocalSource now forms one or more unguarded total identifier/wildcard value
arms. Distinct source-owned binder identities and arm scopes preserve lexical
shadowing, sibling separation and nesting. The scrutinee is formed in its
outer scope. Each binder read aliases its original value endpoint and has a
pure evaluation effect. Every arm value constrains the fresh Catch result;
the scrutinee and every arm body's computation effect constrain the output.
These are the existing finite-join construction applied to actual children,
with child-owned occurrence slots. No effect subtraction is performed.

Ascriptions retain the canonical peeled child index and refresh the endpoint
after binder installation. This avoids another wrapper scan on each visit.
Definition-owned graph traversal follows the new children and retains distinct
Catch binder Values. This gate adds no Catch-result reference fragments or
incoming Expression edges. Full source-global graph coverage and transfer of
formal-registration metadata through these aliases remain unverified.

Focused execution exposed leading trivia in IdentifierExpression nodes at
Catch boundaries. The owning HIR extractor now reads the authentic Identifier
token, rather than treating the entire node text as a name. The same repair
applies to operation-family heads; comments/newline regressions cover both.
No source-text reparsing or trimming is used.

The [playground example](../../tools/inference-playground/examples/catch-value.yu)
passes the Int/Str conditional union through the Catch binder. Both constant
conditions preserve both bounds; an incompatible Int annotation conflicts
and the CLI withholds observations. README scope and CatchBinder rendering
are updated. Operations, resumptions, guards, labels and non-total patterns
remain unavailable in this private carrier, not rejected language features.

Added source/constraint passes visit expressions or arms linearly. Existing
wrapper preformation costs are unchanged; no new global scan or watcher is
introduced. Static inspection found no material new performance uncertainty
requiring a separate performance reviewer. Timing/benchmark budget consumed: 0.

## Proof result and its exact open bridge

The bounded `prover` lane derived the
[native residual primitive P](../theory/2026-10-14-native-handler-residual-cut.md):
`s <= Allowance(J, fresh gamma)` realizes the least plain residual `S \ J`,
conditional on successful native processing. Existing opposite-bound replay
handles current/future source lowers and gamma uppers. Capture incidence,
extrusion, freshening and qualifying intrusion preserve this ordinary
relation and distinct view lineage. No new watcher engine is necessary for P.

Fresh independent `compiler_referee` review accepted this pinned primitive.
The primary repaired the minor source-premise wording: protected same-family
survivors must bypass its plain filtered input; a contextual alternative
requires its own established consumer law. This does not establish source
invariant U or all-model residual equality. The result is consumed as the
native primitive for the next source constructor, with U owned by formation,
typed transport and handler selection. Existing hygiene proofs are reused at
those owners. Full eligibility, ordered coverage, protected future paths,
outside/raw-resumption correspondence, soundness, principality and F5 remain
OPEN. The normal-return implementation does not claim to discharge them.

Actual proof dispatch requested the registered `prover` role with Sol/high;
effective runtime model/effort was not exposed. No child delegation, executable
proof probe or timing experiment was used. The proof records its original
baseline and dependency hashes; the concurrent normal-return source changes
do not modify its native effect/replay/lifecycle owners.

## Review convergence

The normal-return code received independent `compiler_referee` semantics review
and `regression_auditor` sibling/public-surface review. One major fixture
defect used value-only `: int` to claim effect purity. Existing annotation
contracts require `: [] int`; the correction retained the rejection assertion
and did not alter compiler semantics. The same repair batch strengthened
callable/fresh-use result bounds, rejecting uses, each individual versus joint
effect allowance, direct/grouped binder ascriptions and identifier trivia.
Both reviewers closed their findings by delta review. A final regression
delta review accepted the example, CLI assertions and README. No extra panel
or broad re-audit followed. All producer leases are frozen.

The separate [operation-pattern proposal](../design/2026-10-14-operation-pattern-tails.md)
has passed M2 compiler/recovery and exact-conformance review after one repair
batch and a foreign-close clarification. It specifies shared path/glued-call
tails, exact member retry/frontiers and generic structural diagnostics.
Explicit user approval remains pending. No parser code was changed. Approval
unblocks that construction, then operation/payload/raw-resumption formation
with authentic eligibility evidence; parser completion alone will not close U.

## Verification

Primary-owned Cargo invocations were serialized with
`CARGO_BUILD_JOBS=2 timeout 300s`; test commands used `--test-threads=1`.

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-hir --features shadow --test catch_local_source --test conditional_local_source -- --test-threads=1` | 3 + 6 passed |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_catch_value_source -- --test-threads=1` | 6 passed |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_conditionals --test candidate_effect_annotation --test candidate_annotated_primitive_formals --test candidate_intrusion_observation -- --test-threads=1` | 10 + 17 + 21 + 3 passed |
| `test -q -p yu-playground --test cli -- --test-threads=1` | 17 passed; actual CLI process fixtures include the new example |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib positive_extrusion_retains_mixed_allowance_before_capture_and_late_lower -- --test-threads=1` | 1 passed |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib multiatom_view_copy_is_shared_and_member_tails_freshen_with_the_view -- --test-threads=1` | 1 passed |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_value_graph -- --test-threads=1` | 7 passed |
| `check -q --workspace` | Passed, no warnings |

Total final focused tests: 92. Earlier owning checks caught the missing
CatchArm scope consumer, trivia extraction and incorrect pure-effect fixture;
all were repaired at their owners before these final results. Builds/tests
are deterministic evidence, not proof or independent review.

`git diff --check` and local Markdown link checks passed. No full workspace
test suite, benchmark or parser suite was run. The known solver-to-core
development dependency and unrelated recursive fresh-use observation mismatch
were not changed or rerun. No omitted check is represented as passing.

## Integration

Primary synchronization covers `tasks/current.md`, `tasks/research-lab.md`,
`notes/design/INDEX.md`, the proof's acceptance status, the reviewed pending
parser proposal, playground README and this checkpoint. No shared record is
silently deferred. The pending negative-formal question directory remains
unstaged and excluded. Its old answer does not approve a complete field map.
Integration is on `research/simple-sub-intrusion`; no frozen-main changes or
production cutover are included.
