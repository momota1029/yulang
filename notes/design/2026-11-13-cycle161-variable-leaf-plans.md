# Cycle 161: finite current leaf plans

`GeneralDictionaryVariableLeafPlans.LeafPlan` explicitly stores a visible checked
terminal declaration, matching declaration key/role, one bare-variable query and
input name, empty requirements and demanded outputs, a located current source
interval, and its endpoint subtype relation in the common assignment. It does
not contain Instance, Evidence, selection, BranchModels, or an execution premise.

Given global current source Models and Metadata:

1. `instance_of_plan` and `evidence_of_plan` derive each leaf Instance/Evidence.
2. `children_evidence` consumes an All₂ relation between an arbitrary finite
   child list and key list, each pair having a nonempty LeafPlan, and constructs
   All₂ Evidence for the list `keys.map (node · [])`, preserving multiplicity
   and ordering.
3. `parent_evidence` combines a genuine current parent Instance with those
   plans, with no child Evidence premise.
4. `transport_parent_evidence` first uses the cycle161 nonterminal parent
   transport theorem on an old parent Instance, then builds Evidence for every
   actual current child from plans. It retains all checked-registry, shape,
   variable-clause, input-name, query, located-root, source-model, and metadata
   hypotheses of that construction. It does not require old child Evidence.

The location/order premises are substantial obligations, not assumed computed
success or a desired evidence conclusion. This handles bare-variable terminal
children only. It does not prove arbitrary recursive child coverage, selection,
Stable, or general V5 completion.

Direct Lean4.35.0 --trust=0 and all five theorem axiom checks pass without
warnings, only propext/Classical.choice/Quot.sound. The transport theorem imports
the sibling `GeneralDictionaryNonterminalNonpointEvidence` module integrated
by the parent worker. No full build or language CLI result claimed.
