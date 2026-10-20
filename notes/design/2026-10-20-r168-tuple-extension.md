# R168 tuple extension — Luna design lane

Status: **candidate design only; code leases NONE; implementation not approved**.
Sprint: `ordered-tuple-construction-20261020-r168`, contract revision 1,
SHA-256 `cb33b37ce48b7b2131e56cf3c3e510c5e24ac9177f743145966abf94479b8ce8`.
Frozen source baseline: `6cd25179e573fc5ff822b0626f0ad440e7c58f89`.

## Source boundary observed

The syntax parser's parenthesized owner retains ordered child expressions and comma tokens, including a trailing comma. `crates/yu-hir/src/module.rs`'s ordinary admission projection currently accepts a parenthesized form as `Group` only when it has one child and no direct comma or recovery separator. `crates/yu-hir/src/module/local_source.rs` likewise rejects any direct comma/separator and otherwise distinguishes empty parentheses as `Unit` from a one-child `Group`. This is the right admission seam for retaining an authenticated tuple constructor, but syntax punctuation alone does not decide malformed/trailing-comma arity or source recovery behavior; those decisions must follow the adopted R149 syntax contract and the proof matrix.

R149 requires arbitrary finite ordered products. A tuple must be a distinct source/HIR constructor with ordered element identities. It cannot be represented as nested pairs, a Group, or a Unit. The inference layer needs a type constructor whose child sequence preserves each element position, with equal arity and positional relation. The runtime needs a tuple instruction/value retaining ordered element handles and source provenance; evaluation must request each element once from left to right. These are design constraints, not evidence that current solver/type consumers admit the extension.

The proof lane's first consumer pass found two separate inference/type surfaces. `CandidateInference::export` publishes the retained candidate graph, whose public `children()` returns a fixed four-element array; `render.rs` currently treats structural nodes as Function. The older closed-scheme/F5 path in `yu-types` has its own draft, normalization, replay, materialization, generalization, and binder-substitution consumers. Tuple support cannot change one surface and imply the other. The matrix is still in progress, so exact successors and public exposure remain unresolved.

The runtime path also needs a correlated element-receipt representation: the existing handles alone do not show that each tuple element's actual `ReceivedValue` view survives tuple construction and cloned raw-continuation frames. The eventual frame/value design must preserve each position's received view together with its source identity and result handle; borrowing or cloning a bare handle list is not enough.

The term interner currently clones each node into its page, deduplication key, and rollback route journal. An arbitrary-length product cannot be added by changing only the node's inline size or child accessor; ownership, allocation accounting, deduplication, and rollback behavior must be covered at all three storage sites.

## Conditional layer plan

1. **Syntax and source identity:** use the existing parenthesized comma structure; preserve each element's actual source occurrence/range and parent tuple identity. Reject or recover malformed separators through the existing explicit recovery path. Retain the distinction `()` = Unit, `(x)` = Group, `(x,)` = one-element tuple if that is the authenticated grammar, and `(x,y,...)` = tuple. The one-tuple rule must be checked against R149's pinned syntax authority before code.
2. **HIR:** add a dedicated tuple form with ordered `LocalSourceIndex` children and an ordinary `ResolvedExpr` representation if the checked inference path requires it. Lower children without reordering; unsupported/recovery children remain explicit, not silently dropped.
3. **Inference/public types:** first decide from the complete matrix which public path R168 actually extends: candidate graph export/render, closed schemes, or both. Add ordered product nodes to every in-scope representation only after enumerating constructors, public child APIs, renderers, traversals, comparisons, recursive/finalization paths, alpha-equivalence, cloning/rollback, and publication. Each generated tuple constraint relates child i to child i, preserves element effects, and checks arity before position-wise traversal. Every changed owner must be present in the successor lease or justified unchanged by the proof matrix.
4. **Evaluation:** add a source-authenticated tuple instruction and tuple runtime value. Use the existing request/continuation machinery to preserve left-to-right single evaluation, exact child provenance, and the actual received element views across continuation cloning. Do not change the binding-root schedule predicate as a side effect: R167-CASE-FETCH-1 already leaves whole-module execution blocked, and an added `Instruction::Tuple` does not receive a fabricated initializer class. No printer/Display role behavior, destructuring, whole-module schedule, or host output follows from tuple construction alone.

## Gate before exact implementation scope

The proof/matrix lane owns the exhaustive constructor/consumer census and the ordered source/native relation. Luna will merge that census into a sequential R168 contract revision listing exact file paths, current hashes, owners, and no broader directories. The revision must receive CLEAN independent prospective review before any code edit. If the matrix spans more consumers than the 2700-second implementation lane can safely cover, or any required source/type law is missing, return `NO_SAFE_CODE_SLICE` and preserve the exact seam. No partial tuple constructor may be admitted while an in-scope public inference or runtime path silently lacks the corresponding case.

Current limitations remain explicit: R167-CASE-FETCH-1 blocks public whole-module execution; R166 ordinary-provider incidence and Replay residual, original inference/evaluator A/B, imports, standard library, roles, primitive resolution, host writes, destructuring, sample compatibility, and production remain OPEN.

No code edits, tests, builds, compiler/runtime or sample execution, Y2/Y3 execution, or generated outputs were made in this design lane.
