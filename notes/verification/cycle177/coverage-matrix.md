# Cycle 177: precise structural coverage matrix

This additive clarification does not revise the published scope review. It distinguishes the unrestricted length of the scalar input list from the restricted branching of the observed nominal request trees. None of these fragments supplies arbitrary output coverage or the general EvidenceNode field.

| Certificate / consumer | Supported structure | Restrictions that remain |
|---|---|---|
| `ScalarIntervals177` scalar inputs | Any finite list of scalar queries, including zero and repeated entries, at any current Candidate focus. Bounds may be nonpoint intervals; endpoint order follows from the registered site's centered model. | No input binders. The terminal version requires no where requirements and no requested outputs. The result is indexed by a supplied centered model, not universal erased-state commitment. |
| `ScalarRequests177` scalar inputs plus requests | The same finite scalar input list and centered intervals. Nonempty named outputs and emitted children are permitted if **every actual materialization request** has the `ObservedClosedRequests.Observed` certificate. | No universal request-certificate producer. Current child Evidence remains an ordered/multiplicity-preserving All2 premise. Output request trees have the restrictions below; arbitrary scalar input-list length does not imply arbitrary nominal output arity. |
| `ObservedClosedRequests.Tree` request target | A scalar observation, or a nominal descriptor with exactly 0 (`nil`), 1 (`one`) or 2 (`two`) type arguments, recursively certified by the same tree. Arbitrary finite nesting is possible within these constructors. | No nominal node of arity 3 or higher. All nominal child edges are point intervals `(child, child)`. No variable-query, row-argument, or unknown/deferred-query constructor. This is a closed observed tree, not every possible nominal structure. |
| `ObservedClosedRequests.Observed` target location | Each request target equals the source name of some current `Fin state.base.slots` slot; the request's normalized translated pattern matches a certified tree at that slot. | A fresh target outside the current source-slot image cannot satisfy this certificate. Even an existing target fails if its observed tree has the wrong shape. “Fresh” here means unlocated in the current source state, not merely recently allocated historically. |
| `ClosedTreeBranch.Shape` input | Exactly one point-located input slot with a `GeneralNominalTreeFacts.Tree`. A `leaf` nominal descriptor has any finite number of type-argument capture bounds; `wrap` adds one recursively inspected child; `fork` combines two recursively inspected children. | This is not a general arbitrary-branching nested input tree. Structural internal nodes are unary or binary; the arbitrary-arity leaf only captures variables and does not recursively inspect arbitrary child trees at that node. Leaf capture bounds may be nonpoint, while wrap/fork child edges must be point intervals. |
| `ClosedTreeBranch.Shape` binders and requests | Injective finite capture names, exact `declaration.inputNames`, tree-query equality, `RootDefined`, and observed actual requests. `Closed177` adapts this certificate to centered Local selection and current Evidence. | The input tree is not the same as the closed output tree: input leaves allow variable captures, whereas request trees exclude variable queries. Rows are unsupported by the leaf/wrap/fork type-argument forms. The output/request part still uses only scalar and nullary/unary/binary closed request trees. |

## Reporting language

Accurate: “arbitrary finite scalar input lists and registered centered intervals, with existing-target closed request trees of nominal arity at most two per node.”

Inaccurate: “arbitrary nominal arity outputs,” “all closed nominal trees,” or “all selected candidates are covered.”

For the separate input-tree adapter, say: “arbitrary-arity variable-capture leaves under unary/binary nominal structure, at one point-located input.” Do not conflate this with arbitrary recursively branching input trees.

The inspected definitions are `GeneralDictionaryObservedClosedRequests.Tree/Observed`, `GeneralNominalTreeFacts.Tree/query`, and `GeneralDictionaryClosedTreeBranch.Shape`. No semantics, source module or published scope-review file was changed by this clarification.
