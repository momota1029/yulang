# R150 initializer construction audit, revision 1

Status: FROZEN conditional source/native evidence with an exact owner obstruction.
Assignment: R150-INITIALIZER-CERTIFICATE-1, revision 1.
Author: `/root/r150_initializer_certificate`; source excerpts contributed by
Luna `/root` through assignment messages; no descendants. This producer cannot
independently certify this artifact. Fresh review and intake belong to Luna.

## Parent and result

The finite parent is R149's unchanged Types (142 bytes, SHA-256
`8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`)
and Console (92 bytes, SHA-256
`ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`)
modules, authentic library resolution, accepted public inference results and
exact ordered host writes. The required Types payload is `(42, Yulang)\n`;
Console requires `hello from Yulang\n` followed by `3\n`. The pair is an
increment toward broader unchanged Y2 examples. Original Simple-sub/evaluator
A/B, R70/R71, source/native generality, soundness, principality and production
gates remain OPEN, with their original quantifiers. No foreign-continuation
quantifier is discharged here.

Actual result: the first missing declaration-to-classification premise has an
identified construction owner: Y2
`crates/infer/src/lowering/expr/mod.rs:271`,
`BodyLowerer::lower_binding_body_expr`. Luna located it in the immutable oracle
tree and later supplied proposed blob `5bbedd550c1edf877f4a7c254548ea02f47bcae8`;
that dependency is not admitted by R150 rev2. Its implementation was **not read**.
This is an unpinned-owner boundary, not a missing-file finding. No per-sample
initializer certificate or source-qualified sample failure follows. The
publication predicate and runtime obstruction remain conditional on that
missing construction result and the complete composed root census.

Applied to the parent: inspect/pin the actual classifier-producing construction
before choosing a root omission rule or changing an initializer runtime branch.
The current evidence supplies no safe compiler implementation boundary. No
sample can be claimed compatible, failing, or free of required initializers.

## Frozen dependencies and provenance

| Input | Identity / SHA-256 |
|---|---|
| R150 rev2 contract | `246edba9d0af7f009e31702ad5ec55db25e491f41bcc20c085e707cb95880657` |
| R149 Authoritative design, current bytes | `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa` |
| R149 rev5 source manifest | `0c44a69e7f6ac5fe32aba8a29b5f439148e99757a0eb31d62f89796ab927d80b` |
| R149 rev10 contract | `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9` |
| Reviewed R149 rev2 checkpoint note | `0ce7e3127519e6a17aeb1f2f6d25b24490fbca4ea3644efaf7e1ea8a7b3420c0` |
| Reviewed R149 rev2 checkpoint inbox | `5d786082cabf7b2ce0f9c463eba13c9b1dc9f0cc1ee8e1f8e9d51a4bb03b2ea4` |
| Historical R149 closure note, read with its original premises | `6f9a7a430f54fe412163ddec7f374ff9a671d7d5ec62fa6cec252e8cb7800828` |
| Historical R149 closure inbox | `180626758eabf2ccfc08dd6ecc2afeed6e59f55c574ca894305aafee7034f955` |

Y3 baseline is `b7b320d0516208ab4f6aeac14b795f99c6f92cce`, tree
`7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`. Y2 oracle is the distinct
repository `yulang2-oracle-capture`, commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; its complete 40-library-file
manifest is R149 rev5. Commit/tree membership is supplied by the contract.

No Git command was run. Local Y3 bytes below were verified by SHA-1 of
`blob <byte-length> NUL <bytes>` against every contract pin. Y2 source premises
below are either reused from the reviewed checkpoint or supplied by Luna's
immutable-object reads in this assignment. The dirty oracle worktree was not
used as source evidence. A raw-object availability check found the classification
blob packed rather than loose; it established no source absence or semantic fact.

## Construction chain and remaining premises

| Stage | Admitted owner / blob | Established evidence and exact limitation |
|---|---|---|
| Declaration body lowering | Y2 `lowering/body/mod.rs`, `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99` | Luna supplied `lower_def_body`: calls `lower_binding_body_expr`, conditionally wraps the result with `thunk_computation` for `info.nullfix`, then calls `finish_binding(..., true)` on success. The preceding body's constructor is the first unpinned owner. Declaration identity, successful body result and evaluation classification have not been joined for every required declaration. |
| Evaluation to fetch | Y2 `typing.rs`, `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` | Luna supplied exact enum/constructor facts: `Computation::value` sets `Evaluation::Value`; `Computation::computation` sets `Evaluation::Computation`; `BindingFetch::from_evaluation` maps these to `FetchValue` and `FetchComputation`; `runs_computation` is true only for the latter. Neither effect-row shape nor a library call's spelling supplies this input. |
| Publication | Y2 `lowering/body/methods.rs`, `086d42bc63f1c12414a42898671dda22c8ac1084`, 293–298, 358–399 | Luna supplied `finish_binding` calling `commit_provisional_binding`, followed by `DefFinished`. Commit stores the body, optionally constrains it, records the fetch classification, then appends `RuntimeRoot::ComputedDef(def)` iff `fetch.runs_computation() && publish_runtime_root`. This predicate does not enumerate calls, successful bodies, publication suppression paths, or declarations. |
| Nullfix exception | Y2 `lowering/expr/tail.rs`, `8289bfdc6a17b2469ae168ac7939d34813fda474`, 455–476 | Reviewed R149 evidence: `thunk_computation` constructs a unit lambda and returns `Computation::value`. This applies only where the actual `info.nullfix` branch is established. It cannot classify other declarations or all imported initializers. |
| File traversal | Y2 `module_map/mod.rs`, `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`, 1818–1824; `body/mod.rs`, previous pin, 726–753 | Reviewed/supplied evidence: `LoadedFileCsts` sorts by module depth/key; `lower_loaded_files_with_consumer_once` iterates `loaded.by_depth()`, resolves module identity, sets source file, and calls `lower_block`. This establishes stored traversal, not the complete ordered initializer vector across composition/cycles. |
| Root composition | Y2 `compiled_runtime.rs`, `29b400c36a61d5d62aa6518ccb26489d49009898`; `module_table/mod.rs`, `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558` | Pins are in R149 rev5. A complete sample-specific root census, imported-root joins and composition/cycle order are not established by this artifact. No absent root is treated as an empty vector. |
| Specialization | Y2 `lib_support/specializer.rs`, `4dfffee1d68b89ea311dd9218bd56d8ab75a42d5`, 55–70 | Reviewed R149 evidence: a computed-definition root becomes `Root::EvalInstance`. This maps an established root; it cannot prove membership in a sample graph. |
| Request branch | Y2 `runtime/engine.rs`, `d920a498c226383776ff265d5d8efddd06d06779`, 23–40, 67–92; `mono-runtime/src/lib.rs`, `cb2b4cc1fb563934567a9cdcbaf8f803510372bc`, 1219–1223 | Reviewed R149 evidence: `EvalInstance` calls `eval_instance`; `expect_eval_value` rejects `Request` as `UnhandledEffect` before common host resolution. `Root::Expr` can pass its `EvalResult::Request` to host resolution. No required sample initializer is shown to produce such a request. |

For a successfully committed binding, the supplied owners establish the local
implication

`evaluation = Computation AND publish_runtime_root = true`
`=> appended ComputedDef(def) => specialized EvalInstance(def)`.

They also establish

`EvalInstance body returns Request => UnhandledEffect before host resolver`.

The conjunction's declaration-qualified antecedent and the body-to-request edge
are not proved for either sample. These implications are applied as tests on
the next construction evidence, not restated as a new parent theorem.

## Y3 constructor and consumer correspondence

All five source blobs below matched the pinned bytes independently in this lane.

| Y3 owner | Blob | Observed carrier / limitation |
|---|---|---|
| `crates/yu-hir/src/module.rs`, 108–150 | `d8c3e696734463a7bf63d05da00f77f57b9982f4` | `SemanticImports` contains optional opaque `CallerEvidenceBinding`; its documented contract does not validate payload meaning. There is no typed Y2 evaluation/publication/composed-order carrier in this struct. An arbitrary payload is not an authenticated initializer certificate. |
| `tools/inference-playground/src/lib.rs`, 291–308 | `9eeaa94180265970a81f9771a7196e4f0d77008d` | Lowering receives `SemanticImports::empty()`; the resulting same `Arc<HirModule>` goes to scoped or ordinary candidate solving. No imported initializer certificate is supplied on this path. |
| `tools/inference-playground/src/runtime/program.rs`, 256–262, 275–308, 625–655 | `fd69daa3d10aeeb4a685766762eef4d80fc0b5de` | `from_hir` traverses `hir.items()`. For bindings it unwraps Forward/empty Block and classifies Apply/If/Catch/nonempty Block as computation; other instructions classify false. It appends Definition roots accordingly and appends Expression roots for expression items. `execution_roots` clones this vector. This is an actual local constructor, with no demonstrated equality to Y2 Evaluation or imported publication decisions. Traversal order is the existing HIR item sequence; authenticated cross-module order remains absent. |
| `tools/inference-playground/src/runtime/machine.rs`, 292–340 | `4bfd5e244a768ef4cfe61b50fff512d5969b3c88` | `start_source_schedule` calls `start` with the retained vector and a selected DefId. `start` resolves definition identities, rejects duplicate definition/expression roots, checks expression code and HIR ownership, and pushes scheduled roots in supplied order. It validates existing local identities; it does not mint an imported classification/order correspondence. |
| `crates/yu-solver/src/candidate_source.rs`, 1544–1545, 1623–1653 | `e03d92dcb6016e726fe2748bcfb3f17d52e17cd2` | Definition action schedules and expression schedules have separate storage/consumers. Expression execution checks source-owner identity and level 1 for both components before driving the schedule; root execution uses `root_definition_positions`. These inference-action consumers establish neither Y2 ComputedDef publication nor an imported runtime-root composition. Preserve their existing generation, propagation, levels and support behavior. |

The inspected Y3 seam therefore supplies local roots and identity checks, but no
certificate linking imported Y2 declaration evaluation/publication/order to
those roots. This is a source/native carrier obstruction. It is independent of
whether the unknown Y2 initializer census is empty, nonempty, effectful or pure.
The Y2 host-request branch is not asserted to be a Y3 machine branch.

## Per-sample census, order, and omitted cases

| Sample | Required imported ComputedDef identities/count | Composed root order | Required initializer reaching Request |
|---|---|---|---|
| Types | UNKNOWN; zero is not established | UNKNOWN across imported modules/composition | UNKNOWN |
| Console | UNKNOWN; zero is not established | UNKNOWN across imported modules/composition | UNKNOWN |

The library-file closure is not an executable-root census. The body-demand
leaf set in historical R149 evidence was conditional on accepted role selection
and did not include an established complete initializer set. Reuse its identity
discipline and warnings, but do not promote its old 34-file lexical inventory
into the corrected 40-file typed census. Reuse the reviewed R149 rev2 runtime
boundary and nullfix owner correction; reject the withdrawn claim that an
initializer request necessarily reaches the common host resolver. No impl-wide
publication suppression, lexical RHS classifier, file-order runtime theorem,
or spelling-based builtin rule is introduced.

Unresolved coverage includes each required declaration's successful constructor
result, nullfix flag, publication flag, nested/generated bindings, imported
root composition and cycles, selected/default method identities, runtime body
request reachability, and the Y3 import identity/order join. This artifact
claims no exhaustive treatment of those cases.

## Exact handoff and stop

- `R150-INIT-CONSTRUCTOR-1`: Luna must sequentially revise the contract to admit
  proposed blob `5bbedd550c1edf877f4a7c254548ea02f47bcae8` for Y2
  `lowering/expr/mod.rs::lower_binding_body_expr` at :271
  and any resulting constructor owners before further inspection. Required
  evidence is a declaration-qualified Evaluation/publication/root census for
  both exact samples in the frozen 40-file environment. Falsifier: a required
  declaration whose actual constructor/publication differs from the census or
  an omitted root altering order, acceptance, output or effect.
- `R150-INIT-CARRIER-1`: Luna's Y3 source-interface/runtime owner must identify
  how authenticated imported declaration identities, evaluation/publication
  decisions and composed order reach `RuntimeProgram::from_hir` and its actual
  consumers. Required input is the reviewed source certificate. Output is a
  bounded owner/API handoff under separately granted authority. Falsifier:
  distinct Y2 classifications/publication/order requiring different runtime
  roots collapse to the same purported carrier, or a foreign identity is
  accepted. Existing opaque evidence alone does not discharge this request.

No compiler change or provisional code slice is authorized. The next action is
the named pin/contract revision by Luna; this worker has reached its stop
condition and does not continue source inspection while review runs.

Checks: metadata/content hashing and admitted source inspection only; no tests,
builds, compiler/sample execution or external contact. One failed `python`
metadata command found that executable unavailable; `python3` performed byte
hashing. No scratch files or descendants were created. Exact new paths are this
note and `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate.md`.
Resource grant: 600 seconds, no expansion; stop is before its cap, unused time
does not authorize another stage or carryover. Requested routing Sol/high
(`gpt-6.1-sol`, high); observed model/effort UNKNOWN. Writer state: STOPPED after
freezing the paired inbox; no unresolved descendant leases. The paired inbox
contains this note's SHA-256; both final byte hashes are returned to Luna.
