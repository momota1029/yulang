# Observed-plan observer bridge

New module: `GeneralRebaseObservedPlan262`. No existing source changed.

The finite state retains one fixed reference Plan as its fact-meaning basis.
`observe` computes proposals from the actual `plans state root` supplied by the
caller for each selected root, not from that fixed reference Plan.
`Compatible` requires `PlanTransport262.Same fixed (plans state root)` only when
root is selected at that state. It is a structural transport premise, not an
assumed conclusion that old/new Models coincide.

`observe_eq` proves function equality with the fixed-reference DynamicSource
observer using facts_eq pointwise on selected roots. `write_eq` and `step_iff`
expose selected-write and step bridges. `completion` transfers actual settle
success, Runs, length budget and quiescence under source-request coverage.
`step_actual` retains one chosen root outside the assignment quantifier and gives
Models(fixed,after) iff Models(fixed,before) conjoined with ClassEffects of the
observed snapshot, chosen root and its selected observed Plan.

This does not produce plans from source, prove their Frame/Ready/packet validity,
permit arbitrary changed binders/declarations, or establish old-Step simulation.
PlanTransport.Same fixes the declaration, constructors, interpretation, binders
and input-center list; the bridge only applies when those structural conditions
are established. It does not require equality of every captured lower/upper bound.

Validation: strict focused Lean4.35.0 compile using `--trust=0 -DwarningAsError=true`
and retained dependency cache;7 explicit declarations audited;4 usage examples
including constant plans and no restriction on unselected plans. Direct audit and
standalone `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle262ObservedPlan.lean`
both exit0. Full outputs: observed-plan-audit.txt and observed-plan-lake-audit.txt.
Only standard propext, Classical.choice and Quot.sound. No whole-repository build,
Yulang runtime check or independent rebuild of this module was performed here.
