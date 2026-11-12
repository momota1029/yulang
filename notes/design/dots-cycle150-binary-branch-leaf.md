# Cycle150: binary nominal fork with independent finite spines

This is EvidenceNode support on the existing general definitions. General V5 remains 6/14 supplied and 8/14 unresolved. No source semantics or execution rule changes.

## New structural class

The inspected root descriptor has exactly two type arguments, each a point interval at an actual child slot. Each child is an independently arbitrary finite unary nominal spine of cycle149. At the two innermost heads there are n and m type-argument intervals, respectively. The total names map Fin (n+m) → Nat is injective; thus binders are distinct both within and across the branches. The innermost binder intervals need not be points. n and m, both spine depths, descriptor names, source IDs, and binder intervals are universally quantified.

This is a genuine fork, not a unary wrapper renamed as a branch. It does not allow a second fork within a child spine, arbitrary branching arity, repeated binder names, nonpoint parent-to-child edges, row parameters, where children, or demanded associated outputs.

## Same-model proof chain

- `GeneralNominalBranchProjection.point_argument_matches` transports a point-valued nominal argument at any actual argument index, not only index 0.
- `append_projection` combines actual report projections under syntactic capture-name disjointness. Cross-branch same-name obligations are impossible because of that disjointness; they are not assumed semantically true.
- `fork_projection` derives both branches' complete projection constraints from the unchanged current source model, actual descriptors and injective/disjoint names.
- `fork_bindings` derives exact concatenated capture allocation via Fin (n+m). `fork_checked` and `fork_finished` derive real inspection checks and completion.
- `GeneralNominalBranchFacts.private_models` combines those facts with the actual private-state allocation/propagation, deriving both the private state's Models and the report ProjectionModels. Neither is a hypothesis.
- `GeneralDictionaryBranchLeaf` requires only syntax/state/checked-declaration witnesses for its shape. With empty where requirements and no demanded outputs, materialization is empty; `instance_of_shape` constructs an Instance. `selected_leaf` uses current uniqueness to derive the selected key and empty child list, then Evidence for the same arbitrary model. No recorded packet, Joint, Installable, BranchModels, or key equality is assumed.

The results supply a new structural unrecorded-leaf alternative. They do not establish that every reachable stable selected node belongs to this class. They are not a general EvidenceNode bridge or a termination proof. The later `GeneralNominalBranchExample` supplies a concrete nonvacuous fork fixture, described below.

## Verification

Three new modules, 15 public theorems. Each was directly checked using Lean 4.35.0 with `-DwarningAsError=true`, using cycle149's verified dependency build. A separate `--trust=0 -DwarningAsError=true` audit checked all15theorems and printed their exact types; exit0, only standard propext/Classical.choice/Quot.sound. Full output `/tmp/y150-branch-audit.log` is available to the integrating writer. No full build was run. Intermediate elaboration failures were repaired; no sorry, new axiom, or native_decide was used.

## Concrete binary fork regression

`GeneralNominalBranchExample` has three actual source slots. The root is constructor5 with two point children; the children are distinct nullary nominal constructors2 and3. The explicit source assignment gives the root the value nominal5(nominal2(),nominal3()). `state_models` verifies the complete general source Models predicate, and `actual_branch` applies the new structural leaf result to derive BranchModels for that same assignment. `inhabited_branch` records both facts. The declaration is checked independently.

`not_unary_spine` proves that for every finite binder arity/names/bounds and every prior Spine witness at this actual root, its query differs from the new fork query. The leaf constructor would inspect variables rather than nested nominal children; a unary wrap contradicts the actual two-argument descriptor. Thus the example witnesses a real widening beyond the previous unary-spine query class, rather than only a renaming of it.

The fixture has zero captured binders and no associated outputs or where requirements. The general15theorem result above remains quantified over arbitrary n+m distinct binders and independently finite spine depths; the fixture does not on its own verify every such instantiation. It is not asserted to be a stable reachable support state. Five additional public theorem checks and full exact types passed direct Lean `--trust=0 -DwarningAsError=true`, exit0; log `/tmp/y150-branch-example-audit.log`.
