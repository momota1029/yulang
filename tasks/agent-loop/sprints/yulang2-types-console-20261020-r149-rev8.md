# Sprint R149 — unchanged Yulang2 Types and Console execution

Status: ACTIVE_PREPARATION; rev8 corrects the final review attribution and refreshes the conditional budget after rev7 review; no code leases granted
Branch / baseline commit / tree: `research/simple-sub-intrusion` / `b7b320d0516208ab4f6aeac14b795f99c6f92cce` / `7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`
Authority: Authoritative R149 scope at `notes/design/2026-10-20-r149-types-console.md`;
proof plan at `notes/theory/2026-10-20-r149-types-console.md`.
Contract revision: rev8; supersedes rev7 after review found a stale revision attribution.

## Original outcome and success evidence

Original outcome: proof-backed Yulang inference and evaluator behavior that
runs unchanged Yulang2 Web examples as broadly as practical. This sprint
targets the exact pinned `Types` and `Console` templates as a shared-path
increment. It does not redefine the goal as only these two examples.

Original parent obligations: Simple-sub/evaluator A/B, R70/R71, source/native
correspondence, soundness, principality, and production admission remain OPEN.
This sprint supplies finite source-to-runtime evidence; it does not close
those general claims or authorize a production cutover.

Exact source and outputs are pinned in the Authoritative R149 design adopted provisionally by the user. Success requires
the complete 142-byte and 92-byte source templates unchanged, accepted public
types for `id`, `answer`, `name`, and `pair`, Types output separated from
execution values, and exact ordered host-write payloads. CLI and Web consume
the same accepted module/HIR and actual pinned standard-library definitions.
The Types payload is `(42, Yulang)\n`; Console payloads are
`hello from Yulang\n` then `3\n`.

Before/after evidence: currently there is no standard library in this Y3 tree;
`yu-types` has no tuple node; the playground exposes only selected-definition
execution; `run` rejects unhandled requests. After the sprint, the two pinned
examples must pass the contracted CLI and Web checks, with proof/review receipts
for tuple type construction, authentic library resolution, mixed module order,
host request continuation, and atomic publication.

Known prerequisites: exact source-owner
map for tuple syntax/HIR/type/solver and standard-library resolution; an
identity-bound host response path for `out::write`; a module entrypoint that
does not invent a selected definition while preserving the existing mixed
source schedule. R148's 120 seconds do not carry forward.

Current owner evidence narrows that map: `yu-syntax` retains comma-delimited
parenthesized syntax in `crates/yu-syntax/src/expression/delimited.rs`;
`crates/yu-hir/src/module/local_source.rs` rejects any comma/separator in a
`ParenthesizedExpression` before creating `LocalSourceForm`, and
`crates/yu-hir/src/module.rs` also excludes direct comma/separator from its
ordinary admission path. `crates/yu-types/src/lib.rs` currently represents
positive and negative types with only primitive, quantified/recursive,
function, union/intersection forms. `tools/inference-playground/src/runtime/program.rs`
and `runtime/machine.rs` have no tuple instruction/value. No standard-library
source tree was found in the Y3 workspace; `SemanticImports` is supplied to HIR
from outside the source text. These are implementation owners to verify at
activation, not approved language decisions or granted write leases.

Non-goals: changing either Y2 source or expected output; spelling-based
intrinsics for `say`, `println`, `show`, or `out::write`; suppressing effects;
rewriting module expressions as `main`; claiming general Y2 compatibility or
closing any parent proof/adoption gate.

## Two continuing lanes

Proof/source lane (fresh assignment after rev7 review, source-only): a `prover` constructs the exact
identity-bound dependency map for the two pinned examples: imports/re-exports,
source and type/role dependencies, Add/Display candidate prerequisites and
selected implementations, required imported-module computation initializers
and their order, and the reachable primitive leaves. It compares authentic
Y2 owners at the pinned commit and records unresolved premises where the Y3
resolver/solver does not yet provide a corresponding carrier. It must not assume
an unimplemented Y3 resolver, method selector, initializer schedule, or runtime
transition. Apply the resulting graph to the concrete R149 owner/activation
blocker. The prior 600-second grant remains fully charged. Its elapsed time is UNKNOWN: the inbox records an approximate start and exact stop, and explicitly marks runtime telemetry UNKNOWN. Therefore no remainder is available and the old writer is not resumed. Rev1 remains immutable, provisional research; it is not accepted as established evidence until fresh independent review. Rev7 grants a fresh 300-second source-only assignment only after this exact contract receives CLEAN prospective review. The assignment may read rev1 and pinned oracle sources, but writes only `notes/theory/2026-10-20-r149-source-owner-closure.md` and `tasks/agent-loop/inbox/20261020-r149-source-owner-closure.md`. It neither edits nor adopts rev1. Falsifiers: omitted
visible candidate changes selection/ambiguity, omitted initializer changes
module behavior/order, omitted prerequisite changes acceptance, or any required
leaf outside the three sample evaluator primitives. The lane cannot close the
full finite implementation chain or any parent A/B gate.

Complementary source attack: Luna checks pinned Y2 constructors/consumers and
searches for counterexamples to module order, polymorphic element instantiation,
method selection and continuation ownership. This is not proof self-review.

Implementation lane: no code writer is active or leased in rev7. Luna grants
an `implementer` exact per-file leases only after source closure, initializer
order, role selection API, primitive identities, solver consumers, baseline
dependencies and R148 handoffs are frozen and fresh prospective reviews are CLEAN. Expected paths include
`crates/yu-syntax/src/expression/delimited.rs`,
`crates/yu-hir/src/module/local_source.rs`, `crates/yu-hir/src/module.rs`,
`crates/yu-types/src/lib.rs`, exact tuple constraint/type owners in
`crates/yu-solver/`, `tools/inference-playground/src/runtime/program.rs`,
`runtime/machine.rs`, the standard-library/module resolver if one is added,
`tools/inference-playground/src/lib.rs`, `apps/yulang-wasm/src/lib.rs`,
`web/playground/src/main.ts`, `web/playground/smoke-test.mjs`, two exact fixtures,
and finite parser/HIR/type/solver/runtime/playground tests. These are planning
owners, not current leases. Activation must resolve the solver and resolver
owners, then replace this set with an explicit nonoverlapping per-file list and
exact hashes. Production promotion remains unauthorized while parent gates
remain OPEN.

Both lanes are intended to progress in parallel after activation. A proof
obstruction does not stop independent implementation whose semantics are
authoritative. A semantic/source contradiction returns to Luna; workers cannot
revise this contract, add paths or claim authority. No Astra assignment is
proposed: no named risk currently justifies the resource.

## Frozen source map and pending implementation-owner resolution

Y2 oracle baseline: repository `yulang2-oracle-capture`, commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; all entries below are exact Git
blob IDs from that commit. The source-resolution closure is derived from the implicit `mod std;` root,
all reachable module declarations/re-exports and every `std::` module reference
from the sample imports; the resulting 40 source files have no unresolved module
reference. This corrects rev4, whose 34-file traversal missed the injected root
and module-declaration edges. The exact closure is:

```text
lib/std/bool.yu cd973c6baefcfa174b72fc356e355dbbfb854bd9
lib/std/control.yu 3586055834a9574029928487247833a21cef11bf
lib/std/control/flow.yu 7cffe3d504c222f3142b3429eb81543109b0d066
lib/std/control/junction.yu b746d09d51144d31d9da3bc48f9ec2c270fd4d41
lib/std/control/nondet.yu 389afb8c66494fb309e448bc9fe80764a0f7b7d6
lib/std/control/throw.yu 23465a542a61c2b0870c4f048affd5e4de4c93d7
lib/std/control/var.yu ef74a9c2f39fd8e0fe62c3a6ba6eb38554f01f10
lib/std/data.yu 85d1e381d7db2f94c41d7d700625ce5e99fe584e
lib/std/core.yu 2b72ccbaf5ec50d5f0ea75ccc3f108e6b3c38642
lib/std/core/cmp.yu b357d106301e56d6fb77a256a08f52b93060ef98
lib/std/core/convert.yu 1eb1c306435091066b00614a7d1f4a2ee08a9353
lib/std/core/fmt.yu fd7b6607094c9ad70bde1fd41890363fa8bd6b31
lib/std/core/ops.yu 575e6fb15ce2d91a39004bbc7b842fedb2d83fdf
lib/std/core/seq.yu 716c3747c5ce4757f4000b75792ee05b0d859ca9
lib/std/data/fold.yu 041b9c9cc0160ad6e5a3c4e9512abe298c5d53d1
lib/std/data/index.yu 728f69e320b416a06366cf57fb47931db41f8949
lib/std/data/list.yu bd1b9b64d61cf5219199bc50275d8da703ecda54
lib/std/data/opt.yu 956126d039ad4ba05a37aa7af18b51642472bf60
lib/std/data/range.yu 3dcb4336d59ad04ea79b92802749f2f0d5ec57be
lib/std/data/result.yu 2eb83dbf03da7d0a90bc8e45008160808fabc02f
lib/std/float.yu c4c9234e891c8d344ba6c7500f0a39c808864624
lib/std/int.yu 198b8c2d1ba157e3a9507d1f9353f1bc8df9520c
lib/std/io.yu 4e1852f94f9d5c5c2c47f65bc7b75374a9418f93
lib/std/io/console.yu 8c8eabe69755d28bc66a850745f5ea72c136cd74
lib/std/io/file.yu f235091cff71fac5600c3601e3ca1646fa82765f
lib/std/io/net.yu 5787e6e10df93b90a277d9f6e66ff849200a236c
lib/std/num.yu 1edbea1b044f8539e263da5de979dee132673ea5
lib/std/num/frac.yu b8a003efa8177dc064624b40833c4ef38b91564a
lib/std.yu e677e9bce665bc007f9e05e3926b80ccd020eb02
lib/std/prelude.yu e31685be6f17a516b47c3c29c3a124d7ff1c3682
lib/std/testing.yu 0242bdce12bdd21f11248fbd57abee8d33260c69
lib/std/text.yu db9410050c91b6fbf374ae364b1e8c80a14464ea
lib/std/text/bytes.yu 31489155eee5631307c9b77a02fbf25755aee95f
lib/std/text/config.yu c7361dd73fe633bb4a926b2044362f60af97db94
lib/std/text/char.yu d879c7d4a5855da0c7581c84b1406f3571cd1756
lib/std/text/parse.yu 1691990905d51c11cda09cc6059080c6abb7be96
lib/std/text/path.yu 46a843f6ba24116b472b876b0121135c3cee8179
lib/std/text/str.yu 79e607f994b96b75a9b1d93e1b442d9a8101d44d
lib/std/text/yumark.yu 7a6871a15afd28af64c557d6ce5695cf03e7debd
lib/std/time.yu e87ef48ce7920ca3a80d4903a1d0eefbfdeec80e
```

The direct sample roots are `prelude.yu`, `io.yu`, `io/console.yu`,
`core/fmt.yu`, `core/ops.yu`, and `int.yu`; the implicit root `lib/std.yu`
introduces all module declarations that produce the six additional files in rev5. Primitive leaves not backed by these source files
do not currently have equivalent Y3 runtime owners; exact implementation paths
are frozen in §Y3 owner evidence below before code leases.

Read-only source-owner map: syntax in
`crates/yu-syntax/src/expression/delimited.rs`; HIR admission and source
identity in `crates/yu-hir/src/module/local_source.rs`, `module.rs`,
`module/source_annotation.rs`, `source_identity.rs`, `shadow.rs`; tuple/type and
solver paths in `crates/yu-types/src/lib.rs` and `crates/yu-solver/src/`;
playground library resolution and schedule in
`tools/inference-playground/src/`, runtime in `runtime/program.rs`,
`runtime/machine.rs`, `runtime/receiving.rs`; CLI/WASM/Web at the paths enumerated
in the revised implementation handoff. Exact writable paths remain ungranted until
the prospective source review resolves the solver submodules, primitive owners,
and any library resolver additions.

## Pinned Y2 loader and schedule owners

These immutable owner blobs ground the implicit standard-library root, embedded
file collection, compilation unit ordering, ComputedDef production and runtime
root vector consumers. They are source owners, not evidence that all roots are
initializers or that compilation order equals runtime order:

```text
crates/yulang/src/stdlib.rs 22eb01ef3b7b020a1779409d6dd2de9d9af64380
crates/yulang/src/source/std_sources.rs e8af0c059373699101d53454ab7231a7c85827db
crates/yulang/src/source/mod.rs 6472d8fb4268bdd08757eef4aeaf1bf65fedc2b0
crates/yulang/src/source/compilation_units.rs 7a710f438ecaaaa3ef54af5238c6bd419b294edb
crates/infer/src/lowering/body/methods.rs 086d42bc63f1c12414a42898671dda22c8ac1084
crates/infer/src/compiled_runtime.rs 29b400c36a61d5d62aa6518ccb26489d49009898
crates/infer/src/module_table/mod.rs 1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558
crates/specialize/src/lib_support/specializer.rs 4dfffee1d68b89ea311dd9218bd56d8ab75a42d5
crates/infer/src/builtin_ops.rs 2fcddfe8015df988e7c05ce23651c63467719d96
crates/mono-runtime/src/lib.rs cb2b4cc1fb563934567a9cdcbaf8f803510372bc
```

`lib/std.yu` is loaded through `IMPLICIT_STD_MODULE_DECL = "mod std;"` and
the embedded source table. The exact module-file closure now has 40 files; the
initializer census and order remain UNKNOWN until the proof packet traces
production root classification and module composition across cycles.

## Y3 owner evidence and activation boundary

Required primitive semantics are the pinned Y2 definitions: `std::int::add`
for `int -> int -> int`, `std::int::to_string` for `int -> str`, and
`std::text::str::concat` for `str -> str -> str`, respectively backed by
`builtin_op::int_add`, `builtin_op::int_to_string`, and
`builtin_op::string_concat`. Oracle implementation references are
`crates/infer/src/builtin_ops.rs` lines 133, 188 and 271, and
`crates/mono-runtime/src/lib.rs` lines 699, 737 and 804. Y3 has no equivalent
owners today. Candidate Y3 seams are `crates/yu-hir/src/module.rs` for
identity-bound declaration resolution, `crates/yu-hir/src/module/local_source.rs`
for retained primitive references, `crates/yu-solver/src/candidate_source.rs`
and its exact downstream tuple/scheme/call consumers,
`tools/inference-playground/src/runtime/program.rs` for instruction/lowering,
`runtime/machine.rs` for evaluation, and `tools/inference-playground/src/lib.rs`
for the authenticated library/primitive environment. The prospective compiler
review must freeze the exact solver consumers and any new primitive module/API.

The CLI whole-module entrypoint must include
`tools/inference-playground/src/main.rs` (argument parsing and selected-definition
dispatch), in addition to the library API, WASM `apps/yulang-wasm/src/lib.rs`,
`web/playground/src/main.ts`, `web/playground/smoke-test.mjs`, exact fixtures and
CLI integration test. The current CLI requires `--run DEFINITION`; whole-module
execution needs an explicit mode while retaining the selected-definition mode.

Proof handoff: `notes/theory/2026-10-20-r149-types-console-evidence.md` and
`tasks/agent-loop/inbox/20261020-r149-proof.md`; these two proof paths were
originally frozen under rev4 and remain immutable. Implementation handoff:
`tasks/agent-loop/inbox/20261020-r149-implementation.md`. Exact implementation
handoff pins and nonoverlapping compiler-code leases are set only after the fresh
prospective compiler/source review confirms the complete resolver, solver,
primitive, runtime and CLI path. R148's STOPPED writers have acknowledged cessation; Luna may
explicitly supersede their FROZEN solver leases at activation. Unknown board and
R104 leases remain quarantined/held.

Reachability constraint: Y2's 40-file source closure references 59 builtin
operations, while the samples require only the three leaves listed above. The
resolver may load authentic declarations and compile the sample's reachable
definition/role closure, but must retain imported signatures, role prerequisites,
selected implementations and all required computation initializers. The exact
reachability rule and falsifier (any omitted dependency changes acceptance,
selected method identity, schedule or output) remain a prospective design seam;
no implementation lease is granted until frozen.

## Permissions and resources

No compiler-code permissions or source-worker write leases are active before rev7 review. After CLEAN prospective review, Luna may grant one fresh 300-second source-only assignment on the two exact new owner-closure paths listed above. Rev1 stays frozen and the old grant receives no remainder. Luna retains primary ownership of contract, current.json and design index. The full baseline/tree identity and Y2 source closure are pinned; exact resolver, solver, primitive/runtime paths, implementation handoff pins and independent code reviewers remain pending. Unknown writers retain quarantined paths; rev7 does not release the board quarantine or R104 lease.

Fresh cap: 3,000 seconds, Astra 0, no cross-sprint carryover. Charged: owner/source
pinning 300s (including the rev5 60s pin/state update), initial prospective
reviews 240s, prior proof grant 600s, rev5 review 120s, rev6 review 180s and
rev7 review 180s; total 1,620s. Rev8 prospective review reserves 180s. After
review, conditional allocations are source-owner closure 300s, implementation
420s, CLI/Web checks 180s, final review 180s and closeout 120s. Total:
1,620 + 180 + 300 + 420 + 180 + 180 + 120 = 3,000 seconds. Charge each full
reservation when issued; do not refund UNKNOWN runtime or reuse the prior grant's
unverified remainder. Earlier design research before adoption is not charged.
No R148 allocation carries over.

Proposed verification seam after implementation freeze:

```sh
cargo test -p yu-hir --features shadow
cargo test -p yu-types
cargo test -p yu-solver --features shadow-apply-candidate
cargo test -p yu-playground
cargo test -p yulang-wasm
npm --prefix web/playground run typecheck
npm --prefix web/playground run check
```

The Web check builds WASM and the page, then runs `smoke-test.mjs`. Run one
heavy Cargo/build process at a time and keep all scratch/build outputs under
their exact owner. The solver and HIR commands include the candidate/shadow
features that compile the paths under review. Existing package checks alone
are insufficient for success: after prospective review and code-lane activation, add
`tools/inference-playground/tests/yulang2_types_console.rs`, exact unchanged
fixtures under `web/playground/examples/`, and assertions in
`web/playground/smoke-test.mjs` for both fixture byte identities, accepted
public type names/schemes, Types UI output, exact host payloads, write order,
and failure withholding. The CLI integration and WASM smoke path must execute
those exact fixtures without rewriting or injecting `main`. Freeze the test and
fixture paths and hashes in the activated revision. Tests establish finite
behavior only; they do not prove the parent theorems.

Stop on unlisted source owner/dependency, unsupported
runtime operation, source rewrite, output/order mismatch, failed source/native
identity, partial publication, independent-review blocker, confirmed STOP, or
budget exhaustion. Unknown runtime/worker cessation retains its reservation and
lease. Session end leaves no worker recorded RUNNING without current runtime
evidence.

## Frozen seams and handoff

The design and proof plan are immutable reviewed seams. Rev8 is in ACTIVE_PREPARATION: user adoption is settled; source-owner closure and fresh prospective spec/compiler review remain. Freeze dependencies and handoff paths before code leases.

The proof lane must keep finite witness claims distinct from R70/R71, A/B,
soundness, principality, and production readiness. The implementation lane
must connect the same source identity through solver acceptance, schedule
construction, host continuation response, CLI and Web output. Luna alone
adjudicates results and performs explicit-path staging, commit and push.

R148 remains historical `ENDED` / `CLOSED_UNFINISHED_RESEARCH`. Its frozen files
`crates/yu-solver/src/candidate_extrusion.rs`, `candidate_effect.rs`,
`candidate_context.rs`, and related paths remain FROZEN until Luna explicitly
supersedes the STOPPED R148 leases at activation. The
unknown legacy board writer remains quarantined; R104 remains HELD. Rev8
updates `current.json` with the final review attribution; code leases stay empty pending
exact owner/dependency review.
