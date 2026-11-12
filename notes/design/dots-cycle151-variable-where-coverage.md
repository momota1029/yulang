# Cycle151: nonterminal variable where clauses and recursive Evidence

Status: partial proof, not general V5 completion. General V5 remains6/14 supplied and8/14 unresolved.

## What changed relative to cycle150

Cycle150 TreeLeafShape required declaration.requirements=[] and root outputs=[]. The new VariableClauses condition allows arbitrarily many where clauses, with each argument normalizing to a variable and each clause having no named output requests. The root still requests no named outputs. `emission_empty`, `requests_empty`, and `generated_empty` prove only that **materialization equations** are empty. They do not erase actual emitted children or assume that child classification succeeds.

`GeneralDictionaryVariableTree` combines those syntactic results with the existing arbitrary finite binary-tree private-state model theorem. For every current source model it constructs BranchModels, then Instance with the real ordered child list. Actual Local selection supplies common freshness/readiness guards; uniqueness identifies the independently constructed instance with the selected key and children. `selected_evidence` needs evidence for each real child in the very same model.

## Two different recursive composition theorems

`GeneralDictionaryVariableTreeCoverage` uses a freely chosen occurrence domain, CoveredOn (actual historical packets with observation growth, variable-tree syntax, or scalar leaf syntax), and ClosedOn (actual selected children stay in that domain). The mutual induction proves Evidence for every finite Classify dictionary in that domain. No Generated assertion is made for unrecorded children. ClosedOn is explicit, not claimed automatically.

`GeneralDictionaryVariableStableCoverage` instead uses an actual ordinary initial-source trace and a Stable root. For each Generated selected focus, Covered supplies either a recorded packet or one checked visible declaration with Shape at that focus and all its Related alias sites. Each related site also has actual Local selection. The syntax supplies same-model Joint independently of recorded coverage; support stability then supplies actual Generated children. Root stability restricts to each Generated focus using generated_trans. The same finite dictionary induction now needs **no extra domain closure premise and no Joint premise**.

These are soundness-side structural lemmas. They do not implement an executor, prove termination, show every reachable state satisfies the coverage condition, or establish principal results/completeness. Ordinary traces exclude general observation replacement. Shapes retain point internal tree edges, globally injective binder names, variable-only where arguments, and no named output requests. The alias condition requires all related sites to have the same syntactically supported chosen declaration and actual selection. Unrestricted same-input/output aliases are not solved.

## Nonvacuity and limits

`GeneralDictionaryVariableStableExample` applies the stable structural theorem to the actual reachable recursive Display fixture, with a recorded parent and unrecorded scalar child; the complete two-node dictionary is sound in every final journal model. Its alias class is effectively one occurrence. It is not an example of a nontrivial multi-identity alias class or an unrecorded stable nonterminal (the latter is ruled out under the structural criterion).

The separate VariableTree example constructs a genuine nonempty where list and retains its real child. Initial-source reachability is not a claim of stability or execution completion. Those distinctions must be kept in the final report.

## Supervisor termination work

Fresh integration09a135f9 includes the Item4h finite-signature plan and a paper-level sibling-output infinite-schedule analysis. That analysis is not yet a uniform kernel-checked counterexecution. It concerns termination of the update relation, not failure of fixed-state dictionary soundness. Nothing here silently changes that relation or resolves its scope question.
