# Sprint R149-EXACT-SOURCE-READBACK-20261024 — exact parser/HIR source readback

Status: AUTHORIZED by Luna primary; revision 1 frozen before reading the pinned parser/HIR owner contents or writing the provisional driver.
Revision: 1
Branch / baseline: `research/simple-sub-intrusion` / `aba6c8eb9b9caf2559bf955670d662503950c98d`
Primary: `/root`; Luna owns current state, driver, outcomes and Git.
Original goal: implement Yulang type inference and evaluation from established proofs and approved source behavior; commit/push coherent changes and leave the worktree clean.

## Parent outcome and fixed scope

Advance the original R149 Types/Console source→inference→execution admission, without replacing or narrowing it. Construct exact evidence that the unchanged sample and required pinned standard-library source bytes pass through the actual `yu-syntax` parse/HIR construction path, with parser node kinds/ranges/recovery, source keys and declaration identities tied together in one retained process; or report the first authenticated constructor/API boundary that prevents that readback.

The original Simple-sub and evaluator A/B claims, their quantifiers and source domain remain OPEN. This packet does not claim sample acceptance, inference publication, initializer completeness, evaluation, or host output. No source rewrite, injected entry point, spelling-based intrinsic, changed expectation, semantic change, or production-code activation is authorized.

Fixed inputs from Authoritative R149:

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| Types | 142 | `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6` |
| Console | 92 | `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076` |
| Embedded standard-library bundle | 89,288 | `9eb726f179fa407122f1c31f4cd4cf98484bce3052d2486d7d7be84d4ec22b66` |

The exact input authority is `notes/design/2026-10-20-r149-types-console.md` (SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`) and the 40-path/blob closure is `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md` (SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`). Reuse, do not re-prove, the reviewed partial boundary in R149 rev3 outcome `tasks/agent-loop/sprints/r149-current-source-admission-20261024-outcome.md` (SHA-256 `7cd904d92e6318b4af9957b50ac78a0ff04c694e6eabaa0a61fe9e4dd0d10450`) and proof note SHA-256 `d4c6b9e176f9577e20d05dc2fae24b9c0ff68c926525373b3568900acf39db06`.

## Success evidence and method

Success is one of:

1. A reviewed readback for both exact samples and each required provider declaration that reports the actual syntax environment/revision, parser node kind and byte range, complete diagnostics and recovery state, source-key ownership/equality, and HIR declaration/export/member/operation identities. Key equality must be checked on the original key objects in one retained parse/HIR process; ranges, names, Debug strings, or pointers alone do not establish identity. The resulting IDs must join the already-reviewed R149 source/provider path. Parsing success alone does not establish selected-provider acceptance, complete initializer scheduling, inference publication, or runtime output.
2. A reviewed authenticated constructor failure or inaccessible required identity, naming the exact API/source owner and the observation that would distinguish parser/source behavior from an API visibility boundary. Do not infer unsupported language behavior from an unavailable readback.

The one provisional driver must use the real `pinned_stdlib` syntax-environment construction and existing public parser/HIR constructors; it must not recreate either. Record all recoveries and apply the actual downstream acceptance rule, not a blanket “any recovery is fatal” assumption. Compare genuine opaque source-key values inside the same live process and emit local labels plus equality/ownership results. Preserve tuple-Display's separate prerequisites and the authenticated operation family. Keep unknown initializer membership unknown.

The readback is one bounded parser/HIR observation, not a test suite or evaluator run. No `cargo test`, expected-output edits, runtime execution, web/network, or production transition edits are authorized. If existing APIs cannot expose a required fact, stop at that visibility/consumer owner; changing production visibility requires a later exact lease and review.

## Exact source/dependency pins

The baseline commit pins the complete source snapshot. The parser crate root tree is `crates/yu-syntax` Git tree `773fc261b8631fce90143f919d90a4c6426d9668`; its complete transitive `src/` tree is `b4ae511288745b882a6afb951ecaec4fe6d69d16`. Individual direct owners are pinned here for review navigation:

```text
crates/yu-syntax/src/lib.rs                       770a4af4a5832b3210050b4fc5513545569b0ca4718597f67434a714f76f301d
crates/yu-syntax/src/full_parse.rs                dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93
crates/yu-syntax/src/header.rs                    cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad
crates/yu-syntax/src/syntax_environment.rs        fdafdb177c8e2db7a44d66a8d9bc0c1905cc0a22da6457e470a165ca2501c5d7
crates/yu-syntax/src/cursor.rs                    f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142
crates/yu-syntax/src/structural_diagnostic.rs     6cabb3482d24c8a68a65864d6171c09bebcec4d25a305e90a60909d3dce37036
crates/yu-syntax/src/syntax_diagnostic.rs         b3c5e959e646ad3d557c4f60c367d80731bf6a8e616a08326827f687e9077714
crates/yu-syntax/src/cursor/recovery.rs           1e216cf585e5548abc178fab0ebc90b6aef409b22c507dda3e08a52399a45f6e
crates/yu-syntax/src/cursor/recovery/emit.rs      d9866a13f28e1acb1e80f927b64baa4d97f51a5e7934ab5c1d870ea757e497a5
crates/yu-syntax/Cargo.toml                       567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3
Cargo.lock                                        de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5
tools/inference-playground/Cargo.toml             87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
tools/inference-playground/src/lib.rs              45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4
tools/inference-playground/src/pinned_stdlib.rs    3d1a32946e764effd354271653e68edd1b2edaf980f51ea5178ad21adb633d4e
tools/inference-playground/pinned_stdlib.bin       9eb726f179fa407122f1c31f4cd4cf98484bce3052d2486d7d7be84d4ec22b66
crates/yu-hir/src/lib.rs                           4daa2b1753fcf2984c5c27bacb968541c51115ca9f7619d36f8c0e6c7972ef5b
crates/yu-hir/src/module.rs                        6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646
crates/yu-hir/src/shadow.rs                        b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e
crates/yu-hir/src/source_identity.rs               4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23
crates/yu-hir/src/module/local_source.rs           7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1
crates/yu-hir/src/module/source_exports.rs         03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179
crates/yu-hir/src/module/source_role.rs            d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3
crates/yu-hir/src/module/source_impl.rs            558ec50c83040d21fa05e768dffdc46b8a328435b56fc828822a6190ba56a2d5
crates/yu-hir/src/module/source_annotation.rs      409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f
```

Any changed pin returns to Luna before use. The full syntax source tree is the bounded transitive parser read domain; a dependency outside it requires a sequential revision before reading.

## Continuing lanes and exact leases

**Proof/source lane — one `prover`, ≤1200 seconds.** Inspect the pinned parser/HIR owners, derive how exact bytes create source nodes, keys, recovery and declaration identities, and consume Luna's frozen readback receipt. Produce the declaration-qualified correspondence or exact visibility/constructor boundary, then apply it to the reviewed R149 partial trace and state the next source/native premise. Do not claim selection/publication/evaluation from parse evidence.

**Primary evidence lane — Luna/high, initially provisional only.** Inspect the pinned API owners, write one temporary example driver, build/run it once using the pinned syntax environment, retain exact outputs and hashes, then remove only its leased source/output paths after all processes stop and durable receipts are recorded. The driver's exact path is `tools/inference-playground/examples/r149_exact_source_readback.rs`. Scratch manifest/driver output/logs and generated Cargo target are under `/tmp/yulang-r149-exact-source-readback-20261024/`, with exact names: `readback.json`, `stdout.txt`, `stderr.txt`, `command.txt`, and generated `target/`. Use one CPU, one heavy Cargo owner, `--locked`, and one readback execution bounded by 120 seconds. No manifest, lockfile, test, fixture, expectation, public API or production source edits.

The proof writer owns only `notes/theory/2026-10-24-r149-exact-source-readback.md` and `tasks/agent-loop/inbox/20261024-r149-exact-source-readback.md`. Luna owns this contract, `tasks/agent-loop/current.json`, and `tasks/agent-loop/sprints/r149-exact-source-readback-20261024-outcome.md`. Luna is the only writer of the temporary example and scratch output; no child may inspect them while being written. After freeze, Luna gives the proof writer read-only access to the exact driver/output hashes. All generated paths are cleanup-owned by Luna after durable receipts and confirmed process cessation.

## Resources, review, and boundaries

Total sprint cap 3,600 seconds; proof assignment cap 1,200 seconds; primary evidence/build/readback cap 900 seconds; one fresh source-capable independent review cap 300 seconds. Zero Astra. At most one heavy build process and one ≤120-second readback; no evaluator. Preserve all three legacy UNKNOWN reservations. Effective model/effort and session values remain UNKNOWN unless the runtime reports them. No descendants.

Fresh independent `compiler_referee` review checks exact hashes, driver fidelity to the pinned parser/environment, retained recovery evidence, genuine key equality/ownership within one parse, HIR joins, and the report's boundaries. A producer cannot review the result. Luna adjudicates and synchronizes the outcome; only then may an implementation continuation be considered for a demonstrated mismatch.

Stop on changed pins, unavailable source/API owner outside the pinned tree, parser/HIR contradiction, non-deterministic or foreign key evidence, sample byte/hash mismatch, a driver needing a production/API change, resource bound, failed role launch, or worker/session stop. Original A/B and whole-program acceptance remain OPEN. Next dispatcher boundary: a constructor failure, source/native mismatch that enables a concrete code repair, dependency/lease expansion, budget boundary, or reviewed integration.
