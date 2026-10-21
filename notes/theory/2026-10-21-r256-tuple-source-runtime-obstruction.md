# R256 result — Tuple stops after LocalSource admission

Status: primary-only read-only source audit; no independent review. This is a
current-source obstruction map, not a Tuple correspondence proof or an
implementation result. R149, source/native, soundness, principality and
production gates remain OPEN.

## Parent application

The unchanged R149 Types example requires `pair: (int, str)` and the payload
`(42, Yulang)\n` (source SHA-256
`8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`). The
R253/R254 additions provide ordered positive/negative native terms and
same-index live comparison, but do not construct a source Tuple constraint or
evaluate a Tuple at runtime.

## Exact current-source path

Baseline is `93daff511`; these are current HEAD blob IDs:

| Owner | Blob | Finding |
|---|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `c46f60ef6b5c404bb2fc495dd22b2c052a547e98` | A comma parenthesized expression forms `LocalSourceForm::Tuple { elements }`; it allocates one child slot per expression and retains child order. Plain single parentheses remain Group and empty parentheses remain Unit. The same file counts Tuple child capacity in retained source bytes. |
| `crates/yu-hir/src/module.rs` | `d8c3e696734463a7bf63d05da00f77f57b9982f4` | The narrow ordinary-HIR projection declines a comma parenthesized form. `CandidateInference::solve_mode` nevertheless selects an owned LocalSource first, permits its documented placeholder errors, and continues to candidate collection. Thus the projection decline is not by itself the Tuple source refusal. |
| `crates/yu-solver/src/candidate_source.rs` | `6fabb97721e64a02870b04a09f80d8ef294229b9` | The general Work::Visit match has no Tuple child traversal; it falls through without visiting children. Work::Finish later has an explicit Tuple arm returning `unavailable()` at the source-constraint construction boundary. This is the first definite inference refusal after LocalSource construction. |
| `crates/yu-solver/src/candidate_value_graph.rs` | `ecde135d13370889d37a458d08a737d8c616d64c` | `retain_source` has no Tuple child case, and its fallback does nothing. Names nested under a Tuple therefore do not enter this retained Value-reference graph. Generic Tuple support must visit every child here to preserve source-owner reachability and SCC inputs. |
| `crates/yu-solver/src/term.rs` | `daef51e7889bdc2550ac718a8250dc5fa58493c5` | Positive and negative ordered Tuple terms and views exist from R253. |
| `crates/yu-solver/src/lib.rs` | `95162d3d82665b33a5b5a36755df300b72ca3e0e` | Tuple endpoint kinds, exact arity checks, indexed child dispatch and TuplePort context are present from R254. This is downstream of the missing source constraint. |
| `crates/yu-solver/src/candidate_scheme.rs` | `8556246051638fa0db2adac3f16335018cf96511` | Retained/captured `Node` still has only Leaf, EffectOperand, Row and four-field Function constructors. It has no ordered Tuple constructor or FreshUse reconstruction. |
| `crates/yu-solver/src/shadow_apply.rs` | `cc713715d810b29d5b8982313845c3837972e751` | Candidate graph export remains the fixed Function-child API; no Tuple observation is provided. |
| `crates/yu-types/src/lib.rs` | `4ebff48c87c3ee948e3cff77c9339b06927f6a08` | Public positive `PNode` and negative `NNode` have no product constructor. R168's closed-type consumers remain a separate requirement after inference construction. |
| `tools/inference-playground/src/runtime/program.rs` | `fbb8fff537e244a16d0b0305efa0a3acf6394f0e` | `Instruction` has no Tuple case; HIR-to-runtime compilation explicitly returns `InvalidSourceReference` for a Tuple LocalSource form. |
| `tools/inference-playground/src/runtime/machine.rs` | `7fe8a8ce7b5876126123e377c94ce9051f123caa` | `RuntimeValueKind` has no product value. Ordered construction also needs evaluation frames that preserve each evaluated prefix across suspension/resume. |

## Result and next implementation seam

The earliest definite candidate-inference stop is source `Work::Finish`, after
LocalSource has retained the actual tuple. Before that refusal is removed, its
source traversal must visit all children in source order and generate one
ordered Tuple Value constructor plus the per-child effect edges. The
source-derived Value-reference graph must also descend through those same
children. Then Tuple must survive scheme capture/FreshUse and graph export,
closed `yu-types`, and ordered runtime evaluation. The runtime instruction and
frame design must preserve the evaluated prefix through an unhandled request
or suspension; a flat eager re-evaluation would not satisfy the R149 runtime
contract.

No source constructor, native term, narrow test or refusal arm proves this
chain. R168 M1–M20 and C1–C13 remain design obligations, with its prospective
review gate still OPEN. R149's library/import/primitive/whole-module/output
work remains separately OPEN, so closing Tuple alone will not make either
sample pass. No source files or tests were changed in R256.

## Checks and limits

This packet used current source reads and Git blob pins only. No tests, builds,
or sample runs were performed. Independent review and all parent gates remain
OPEN.
