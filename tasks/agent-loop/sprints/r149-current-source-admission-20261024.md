# Sprint R149-CURRENT-SOURCE-ADMISSION-20261024 — source to execution admission

Status: AUTHORIZED by Luna primary; revision 1 frozen before the proof-worker launch.
Revision: 1
Branch / baseline: `research/simple-sub-intrusion` / `22239717efd1a8205be561ae1a8cfae35057d3c9`
Primary: `/root`; primary-only current-state and Git integration.
Original goal: use the established proofs and approved source behavior to implement Yulang type inference and evaluation; commit and push coherent changes and leave the worktree clean.

## Original outcome and success evidence

This sprint advances, but does not replace or complete, the original implementation goal. Its concrete outcome is a reviewed source/native admission certificate for the exact unchanged R149 `Types` and `Console` modules and their actual required standard-library imports, or a precise first unsupported source constructor/owner that explains why the certificate cannot be completed. The certificate must join source declarations and bodies to resolved identities, fetch/execution classification, inferred publication, runtime roots, schedule order and consumers. A source name match, existing test expectation, note count, or CLI exit status is not sufficient evidence.

The original Simple-sub and evaluator A/B claims retain their original quantifiers and source domain and remain OPEN. This sprint neither proves nor refutes them. R149 remains the adopted behavior boundary; no source rewriting, prefix extraction, injected `main`, intrinsic recognition by spelling, changed expected output, or narrowing of supported source is allowed.

Fixed R149 observations and inputs:

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `Types` | 142 | `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6` |
| `Console` | 92 | `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076` |

The unchanged Types pane must expose polymorphic `id`, `answer: int`, `name: str`, and `pair: (int, str)`; its host payload is `(42, Yulang)\n`. Console must capture `hello from Yulang\n` followed by `3\n`. These are fixed authority claims, not results of this sprint unless the exact matching observations are independently obtained under a later authorized execution stage.

Success evidence for this revision is one of:

1. A reviewed finite certificate that identifies the exact source declaration/body and resolved DefId for every required provider, proves the selected source projection and candidate inference are the same accepted module, enumerates required computation roots and their source-order relation, and follows each root through runtime definition lookup/cache, execution schedule and host-operation continuation; or
2. A reviewed precise obstruction naming the first actual CST/HIR/source owner whose declaration, identity, fetch classification, publication, root/schedule membership or consumer cannot be established, with the smallest evidence that would distinguish a source limitation from a Y3 implementation gap.

The proof producer must apply existing R149/R152 evidence instead of repeating completed conditional arguments. R167's `Case` classification and R268's external-`mod`/Missing observation must be rechecked against current bytes; neither historical result is assumed current or closed.

## Authority and immutable dependency pins

Governing behavior: `notes/design/2026-10-20-r149-types-console.md`, SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa` (Authoritative, provisionally adopted by the user's ongoing goal). Exact 40-source Y2 closure: `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`, SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`. Oracle repository `yulang2-oracle-capture`, commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`; template owner `web/playground/src/main.ts`, blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`.

Relevant prior scope records (reuse only their stated conclusions):

- R152 contract `tasks/agent-loop/sprints/yulang2-types-console-20261020-r152.md`, SHA-256 `be08f5522b13b05a321448bd34d39dd6820a4644d843895a9b0612d70e296256`.
- R167 contract `tasks/agent-loop/sprints/source-authenticated-module-run-20261020-r167.md`, SHA-256 `792b2d8f140d7c8bfd0623a452213228fbe731f377b7494cb8f8bc88d116f535`.
- R149 source-owner closure is `STOPPED_UNFROZEN_RESULT`; R167 Case classification and R282/R283 observations are prior evidence only and must be checked at this baseline.

The user-supplied safety manuscripts are supplementary proof constraints, not a substitute for this source/runtime correspondence:

- `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `docs/yulang-source-type-safety-ja.tex`, SHA-256 `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- `docs/yulang-dot-selection-safety-ja.tex`, SHA-256 `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`.

Direct implementation/source owners are pinned by SHA-256 at the baseline:

```text
tools/inference-playground/src/lib.rs                         45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4
tools/inference-playground/src/pinned_stdlib.rs               3d1a32946e764effd354271653e68edd1b2edaf980f51ea5178ad21adb633d4e
tools/inference-playground/src/scheme.rs                      82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0
tools/inference-playground/src/runtime/program.rs             6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907
tools/inference-playground/src/runtime/machine.rs              b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e
tools/inference-playground/src/runtime/continuation.rs         194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs            57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26
tools/inference-playground/src/runtime/dispatch.rs             f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873
tools/inference-playground/src/runtime/primitive.rs             eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85
crates/yu-hir/src/lib.rs                                      4daa2b1753fcf2984c5c27bacb968541c51115ca9f7619d36f8c0e6c7972ef5b
crates/yu-hir/src/shadow.rs                                   b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e
crates/yu-hir/src/module/local_source.rs                      7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1
crates/yu-hir/src/module/source_exports.rs                    03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179
crates/yu-hir/src/module/source_role.rs                       d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3
crates/yu-hir/src/source_identity.rs                          4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23
crates/yu-solver/src/lib.rs                                   ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
crates/yu-solver/src/candidate_source.rs                      57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e
crates/yu-solver/src/candidate_scheme.rs                      02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5
crates/yu-solver/src/candidate_effect.rs                      70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f
crates/yu-solver/src/shadow_apply.rs                          f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d
```

Any dependency/source bytes that differ invalidate the affected certificate and return to Luna; no worker may silently refresh a pin. No external dependency, source behavior, semantic choice or source domain may be added.

## Two continuing lanes

**Proof/source lane — one constructive producer.** Build the declaration-qualified certificate (or exact obstruction) using the Y2 pinned source and current Y3 owners. Trace each required imported binding/member/operator from source namespace and declaration/body identity through source import resolution, `pinned_provider_projection`/selected-member imports, candidate inference/public-type projection, `reachable_runtime_roots`, `RuntimeRootKind::{Binding,LinkedBinding,Member,Operator,Expression}`, `source_computation`, `source_schedule`, `start_module_schedule`, demand/cache behavior and actual consumer. Distinguish a value provider fetched on demand from a computation initializer the accepted interface requires to execute. Inspect `Case` as a possible computation and do not infer eager/lazy policy from its enum tag alone. Record exact source order, count, identity and first unavailable owner.

**Implementation lane — primary, initially read-only.** Independently inspect the current source-import/candidate-world path in `lib.rs` and schedule/linked-root construction in `runtime/program.rs`; map every rejected/accepted path to its producer and consumer. Compare the observed code with the certificate and the three supplied manuscripts' actual preservation invariants. Do not edit these files in revision 1. If a reviewed certificate proves an owner-local mismatch, Luna may issue a versioned continuation with exact implementation leases, bounded code changes and a fresh review; a change to any additional owner, source semantics or proof premise requires a new Luna decision/revision.

Use the commuting diagram `source declaration/body → resolved identity/fetch class → selected provider and accepted inference → runtime root/ordered schedule → cache/demand/consumer → host effect`. Falsifiers include an omitted required imported computation, duplicate or reordered initializer, name-only join where source identity is required, wrong selected member/operator, skipped computation `Case`, dropped effect residual, or type/output publication from different candidates.

## Permissions, resources and stop conditions

Revision 1 grants read-only access to the pinned source and code owners listed above. The proof producer may write only:

- `notes/theory/2026-10-24-r149-current-source-admission.md`
- `tasks/agent-loop/inbox/20261024-r149-current-source-admission.md`

Luna alone owns this contract, `tasks/agent-loop/current.json`, and the eventual outcome receipt. No code, test, expectation, manifest, lockfile, public documentation, question, shared theory index or history-ledger edit is granted to the producer. Initial stage runs no build, test, benchmark, CLI sample, runtime probe, nested CLI, or network fetch. No artifacts are cleaned or deleted. This is a source/code certificate, not an execution observation.

Total sprint cap: 3,600 seconds; proof assignment cap 1,200 seconds; primary audit/parent application cap 900 seconds; fresh independent certificate review cap 300 seconds; reserve 1,200 seconds for a later versioned implementation continuation if review establishes a bounded safe change. Astra: 0. No automatic carryover or renewal. At most one live producer/reviewer/implementer child at a time; preserve all three existing UNKNOWN legacy reservations and reserve review/integration capacity. Actual effective model/effort remain UNKNOWN unless runtime evidence supplies them. No descendant is permitted.

Stop on a changed pin, conflicting source identity, missing required Y2 closure, proof contradiction, semantic ambiguity, unavailable source owner, worker stop/session end, or budget bound. A blocked proof does not stop the independent primary code audit. No result closes original A/B, whole-program source adequacy, public compatibility, or production promotion.

## Frozen handoff and review seam

Producer freezes one coherent certificate and one inbox handoff with actual authors/role/runtime identity, exact hashes, resources, checked source-to-native relation, omitted cases, parent application, first remaining premise and owner, falsifier, all newly created paths, and writer-stop receipt. Luna directly acknowledges intake. A fresh independent `compiler_referee` or source-capable reviewer checks the frozen hashes, source identity joins, initializer classification/order, candidate publication/execution coherence and obstruction completeness; the producer cannot review its own work.

Only after review does Luna choose whether a versioned implementation continuation is warranted. If code changes are warranted, the continuation must pin the then-current baseline and exact edited constructors/consumers, preserve R149's approved behavior, assign an independent implementation review, specify one relevant non-test compile check if needed, and keep sample runtime claims unobserved until exact source execution evidence exists. Luna stages explicit paths, reviews the full outbound range, commits and pushes only a coherent accepted result. Substantial milestones update current state and a durable outcome; unrelated open gates and unknown leases remain recorded.

Next dispatcher consultation: reviewed certificate/obstruction, a source-identity or semantic counterexample, a necessary dependency/lease/resource change, or an integration boundary—not each internal trace.
