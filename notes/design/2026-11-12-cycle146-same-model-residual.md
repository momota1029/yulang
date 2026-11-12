# Cycle146: a narrower route to V5 EvidenceNode (UNPROVED)

The concrete `OutputMergeStable.stable_classified_dictionary` now closes the
nonempty output-merge fixture. General V5 still has 8/14 unproved fields.
No counterexample to the general target was established in this cycle.

The existing `GeneralDictionarySupportComposition.JointAtSelected` is a
sufficient route for BOTH EvidenceNode and GeneratedChildren. It is stronger
than what EvidenceNode alone needs. Do not silently remove the model or
child-Evidence premises from the latter goal.

## Next theorem-shaped obligation

For arbitrary checked registry, tracked state, saturation root, and focus:

- the state is Reachable from I25 Initial;
- the chosen model satisfies THIS state's journal;
- focus is root or Generated from it;
- focus and its immediate children are Stable in THIS same state;
- the actual support Local classifier selects key and children;
- all immediate child dictionaries have full Evidence in THIS model;

prove that there exist a declaration in the registry with this selected key,
its checked proof, and located inspection bounds such that
`BranchModels registry state.current.context focus declaration checked bounds model`.

The model here is the exact given model, not a fresh existential candidate
model. The result is a parent BranchModels witness, not the desired recursive
Evidence itself. `GeneralDictionaryRecursiveEvidence.evidence_node_of_branch`
combines it with the selected Survivor and supplied child Evidence directly.
It does not need all related alias sites simultaneously applicable or all
historical packet keys consistent, as a complete Joint proof would.

## Why it is not already solved

Prepared/Survivor provides SOME branch model. It does not prove that arbitrary
current journal model satisfies that same branch. Child Evidence provides
child Instances in the required model, but does not automatically establish
parent capture compatibility, private merge/self-check atoms, ProjectionModels,
and the full generated materialization. `branch_models_iff`'s raw-context
component is supplied by `Models state.current model`. The remaining semantic
components require a general reconstruction from reachable historical packets
and the actual children, or another argument.

The new equality phases preserve existing Evidence/Joint; preservation is not
creation. The new merge lemmas discharge output equations for specified
historical variable requests; they do not establish all missing parent branch
components. The new ContextComplete preservation theorem assumes completeness
at its starting point, and does not cover arbitrary installs. None closes the
above obligation.

GeneratedChildren has no model/child-Evidence assumptions and therefore still
needs its own argument. Weakening the EvidenceNode route must not silently
upgrade GeneratedChildren or the complete fourteen-field bridge package.
