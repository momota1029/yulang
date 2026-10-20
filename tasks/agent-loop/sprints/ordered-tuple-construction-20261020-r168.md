# R168 — ordered tuple construction through inference and evaluation

Status: proposed, no R168 lease/work started. The fixed parent goal remains proof-backed Yulang type inference/evaluator implementation and broad execution of unchanged Yulang2 Web samples in this repository. R167 closed only its source-order result; whole-module execution remains blocked by R167-CASE-FETCH-1. This sprint follows the separate R149-adopted ordered tuple semantics and does not claim a full sample runs.

## Outcome and authority

Implement ordered tuple construction over actual Y3 source, inference, and evaluator paths, with an independently reviewed constructor/consumer correspondence. R149 already adopts tuples as positional product values with arbitrary finite arity, preserving each element's order and type; pair-only encoding is not allowed. First freeze an exhaustive consumer matrix and a reviewable implementation design. No source/code write lease is granted by this proposal. Luna may add exact code leases only in a sequential contract revision after the matrix identifies every constructor, traversal, clone/finalization, equality/display, constraint, and runtime consumer and that revision receives CLEAN prospective review.

Target behavior is tuple construction in ordinary source expressions, including heterogeneous and nested values, with equal arity and position-wise type correspondence, preserved element effects, and left-to-right single evaluation with authentic element provenance. No destructuring, tuple pattern matching, standard library, imports, roles, primitive bindings, host writes, CLI/Web changes, or sample-wide claim is included. Existing Unit and Group forms remain distinct. The exact syntax, arity rules, recovery behavior, and source identity rules must follow R149's adopted source authority and checked-in parser; missing authority is an exact blocker, not permission to invent syntax.

## Baseline and pins

- Frozen source/code baseline: `6cd25179e573fc5ff822b0626f0ad440e7c58f89` (R167 closeout commit; document-only successor commits do not redefine this byte baseline).
- R149 authority: `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`, SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`.
- R149 adopted design: `notes/design/2026-10-20-r149-types-console.md`, SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`.
- R167 reviewed boundary: `notes/progress/2026-10-20-r167-closeout.md`, SHA-256 `b24bb26e28e6af2b42bc6a48d95b8f013de5224550b137c7bbe6745f479ef7cf`.
- Initial source-owner byte pins at the frozen baseline:
  - `crates/yu-syntax/src/expression/delimited.rs` `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95`
  - `crates/yu-hir/src/module/local_source.rs` `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442`
  - `crates/yu-hir/src/module.rs` `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907`
  - `crates/yu-hir/src/module/source_annotation.rs` `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`
  - `crates/yu-types/src/lib.rs` `c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b`
  - `crates/yu-solver/src/term.rs` `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60`
  - `crates/yu-solver/src/candidate_scheme.rs` `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850`
  - `crates/yu-solver/src/candidate_source.rs` `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7`
  - `tools/inference-playground/src/runtime/program.rs` `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d`
  - `tools/inference-playground/src/runtime/machine.rs` `875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1`
  - `tools/inference-playground/src/lib.rs` `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473`
- Proof producer refreshes all pins and records any additional discovered owner before the matrix is reviewed. Do not treat the Yulang2 oracle checkout or binary as an executable dependency.

## Proof and consumer-matrix lane — R168-TUPLE-CORRESPONDENCE

Producer: `/root/r165_native_admission_proof`, fresh assignment after prospective CLEAN review. Exact outputs:

- `notes/theory/2026-10-20-r168-ordered-tuple-construction.md`
- `tasks/agent-loop/inbox/20261020-r168-tuple-proof.md`

Map authentic tuple syntax occurrences to retained source/HIR nodes, solver terms/constraints, finalized public type views, and runtime instructions/values. Enumerate every constructor, traversal, polarity, clone/rollback, comparison, normalization/finalization, formatting, and execution consumer that must change. Establish ordered positional correspondence: equal arity; position i relates only to position i; element effects and source identity remain attached to the same i; nested/heterogeneous constructors compose; runtime evaluates each element once in source order. Include an explicit table of all touched and audited-but-unchanged consumers, recovery/unsupported syntax, Unit/Group distinction, finite arities, and exact source-to-native premises.

Success identifies a complete constructor/consumer matrix, applies the tuple relation to ordinary tuple construction, and supplies enough pinned evidence for Luna to enumerate exact code leases. If an existing stage lacks a source law or a downstream consumer cannot be covered without broad semantic change, return its exact owner and `NO_SAFE_CODE_SLICE`; do not start code edits.

No code/source/solver edits, tests, builds, compiler/runtime/sample execution, Y2/Y3 execution, instrumentation, generated outputs, or descendants.

## Luna design lane — R168-TUPLE-IMPLEMENTATION-DESIGN

Luna owns `notes/design/2026-10-20-r168-tuple-extension.md` and `tasks/agent-loop/inbox/20261020-r168-tuple-implementation.md`. Prepare the actual cross-layer plan from the current owners, then reconcile it against the proof matrix. Do not propose pair encoding, implicit tuple destructuring, eager execution, or lossy provenance. Code leases remain NONE until an acknowledged sequential revision lists exact files and hashes and receives independent prospective review. Any successor code revision uses the remaining fixed sprint envelope, not a second budget.

## Conditional implementation, review, and resources

Total cap 6000 seconds, charged in full on grant, no carryover: preparation/prospective review 600; proof plus consumer matrix 1500; Luna design and exact code-scope revision 300; conditional implementation 2700; independent proof/code review 600; integration/closeout 300. Astra 0, no descendants, preserve all three UNKNOWN legacy reservations and review/integration capacity. The 2700-second code lane is unavailable until proof/matrix review is CLEAN, exact code leases are listed in a sequential contract revision, and that revision is prospectively CLEAN reviewed.

Independent reviewer: `/root/r157_contract_review`, fresh for every frozen result/revision. Proof review challenges source occurrence identity, ordered type/effect correspondence, the exhaustive consumer table, rollback/finalization paths, and whether the source rule actually admits the claimed arities. Code review checks the full exact diff against the reviewed matrix, position preservation, Unit/Group distinction, provenance, and evaluation order. No author self-certification.

Verification boundary: no tests, builds, Yulang2/Yulang3 execution, sample runs, instrumentation, expected-output edits, or production claims. R166 ordinary-provider incidence, Replay residual, original inference/evaluator A/B, and R167 whole-module execution remain separately OPEN.

Stop on an unpinned owner, incomplete consumer matrix, tuple arity/source-law mismatch, position/effect/provenance loss, hidden eager evaluation, code path outside a reviewed exact lease, unknown writer overlap, or resource cap. Luna alone updates current state, stages explicit paths, reviews outbound range, commits, and pushes.

## Parent limits

R168 advances a reusable inference/evaluator constructor. It does not close imported modules, tuple destructuring, standard library, roles, primitive resolution, host writes, module completion, Types/Console sample compatibility, the original A/B theorem, or production. The user's parent goal remains active after this bounded sprint.
