# Cycle150: arbitrary finite binary nominal trees

General V5 remains6/14 supplied and8/14 unresolved. This extends the structural unrecorded terminal-leaf support, not general reachable coverage.

`GeneralNominalTreeFacts.Tree` is inductively built from nominal binder leaves, unary point wrappers, and binary point forks whose children are themselves Trees. Binary forks may occur at any finite depth; the total number/depth is not bounded. Every leaf descriptor has actual type-argument intervals; leaves may have nonpoint binder intervals. Internal descriptor edges are point intervals. Fin-split binder names/bounds give exact global capture ordering, and a single global injectivity condition excludes all repeated binder names. The certificate contains only descriptors, actual lookups/argument layout and recursive syntax witnesses, never Models/ProjectionModels/BranchModels/Instance/Evidence.

Structural induction derives capture name provenance, full same-model projection obligations, exact capture allocation, completed inspection, all checked source inequalities, and finally the actual privateState Models and report ProjectionModels. Terminal/no-output declarations then yield full BranchModels, Instance, selected key equality, empty child lists and Evidence through `GeneralDictionaryTreeLeaf`. This completes private-state assembly; it is not only a projection lemma.

`ofSpine` and `ofFork` preserve queries. Shape adapters and `spine_covered`/`branch_covered` preserve prior structural coverage certificates without added premises. Nonpoint internal edges, arbitrary arity>2 nodes, row parameters, repeated binders, nonterminal where clauses and associated output obligations remain excluded. Explicit finite structural coverage for every selected focus remains a separate generalV5 residual.

Both modules passed direct Lean4.35.0 warning-as-error checks. Full theorem types and trust-zero axiom checks are in `/tmp/y150-tree-audit.log`; all17public theorems pass, standard axioms only. No full build performed. No source semantics, aggregate or frozen audit file changed.

## Nested two-fork fixture

`GeneralNominalTreeExample` gives an explicit five-slot source and explicit assignment for Pair(Pair(Nominal2(),Nominal3()),Nominal4()). The actual outer and inner descriptors both have two point type arguments. `state_models`, `actual_branch` and `inhabited_tree_branch` verify the whole general source Models and derived BranchModels in that unchanged assignment. The declaration is independently checked.

`inner_not_spine` excludes all unary-spine queries at the actual inner node. `not_single_fork` then excludes every old single-Fork query at the root, for arbitrary candidate binder arities/names/bounds: actual descriptor membership determines the child slots, and query equality would force its first child Spine to match the inner binary fork. This makes the increase beyond the previous single-fork class explicit.

The concrete fixture has no binders, where requirements or demanded outputs, and no stable/reachable-support claim is made. The recursive theorem itself supports arbitrary finite leaf binder counts and arbitrary finite binary nesting; the fixture is a nonvacuity and strict-shape regression, not the justification for those universal claims. The six fixture theorem checks, exact types and trust-zero audit passed (exit0), log `/tmp/y150-tree-example-audit.log`.
