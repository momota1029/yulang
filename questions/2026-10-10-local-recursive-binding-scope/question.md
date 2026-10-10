# Question: local recursive binding scope

Question ID: `local-recursive-binding-scope`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): implementation baseline `5daa64d6a`; Oracle reference `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Task/thread locator: unavailable; no stable conversation identifier is exposed
Governing source/section: `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md`, §3; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation”; `notes/progress/2026-10-10-generic-local-source-hir.md`, “Implementation”

## Requested scoped decision

Choose whether a local function binding may refer to itself while its initializer is inferred.

This does not choose mutual local-recursive groups, polymorphic recursion, a new annotation rule, or a change to sequential visibility between sibling bindings.

## Current evidence

The active Yulang3 source carrier deliberately publishes a local name after its initializer and describes local initializers as sequential and nonrecursive. Consequently, `my outer = { my loop x = loop x; loop 1 }` is not accepted by the candidate inference path.

The frozen Oracle at `a58eefc31e22141574b6f20c6a5748151c6d79f1` has an explicit recursive-lambda lowering path. Its `recursive_lambda_lowers_to_local_self_binding` test verifies the lambda body and continuation both refer to the same local definition. Its `local_recursive_binding_scheme_keeps_argument_effect_passthrough` test exercises a recursive local `loop` function inside a block. This is compatibility evidence, not by itself Yulang3 implementation authority.

The Authoritative nested-block addendum §3 explicitly leaves recursive local definitions undecided. The current parent-copy SCC decision requires actual recursive SCC integration, but does not specify local self-binding scope. A primary probe of `my outer = { my loop x = loop x; loop 1 }` fails with candidate `Unsupported`; no production source or solver behavior was changed by that probe.

## Options and consequences

1. **Support a single local self-recursive function binding.** Make that binder visible in its own initializer. Infer the initializer against one open monomorphic live root; recursive occurrences constrain that same root. After the initializer's intrinsic constraints exist, retain the existing live local root and boundary for later capture/freshening. Keep sibling bindings sequential and exclude mutual local-recursive groups and polymorphic recursion. This matches the observed Oracle direction and requires coordinated HIR scope, solver scheduling, rollback and focused source tests.

2. **Keep local bindings nonrecursive.** Preserve the current sequential scope: a local binding is available only after its initializer. Apply the recursion requirement to module-level SCCs; do not extend it to local self-reference. This avoids a new source-meaning change but leaves the Oracle local-recursive example outside the Yulang3 supported behavior.

Choose option 1 or 2. No option changes the existing parent/copy SCC equality, live-let extrusion policy, annotation hygiene contract, or complete Call contract.

## Affected work

Blocked scope: accepting local self-reference in an initializer, including HIR identity formation and its open-root to live-scheme transition.

Independent authorized work: continue module-level recursive SCC coverage, local nonrecursive polymorphism, effect annotation transport, operation/Call construction and public migration without assuming local self-recursive scope.

## Publication

Keep this question directory unstaged and uncommitted until an explicitly approved answer is validated and integrated with its matching question/draft/answer bundle. The questioner retains all Git operations.
