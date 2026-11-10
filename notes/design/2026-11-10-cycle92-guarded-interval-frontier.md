# Guarded interval diagnostic frontier

Status: Draft. Date: 2026-11-10. Scope: fixed Form endpoints, cycle92.

## Partial goal and governing decisions

Produce the complete finite diagnostic tree before selecting complete plans.
Retain each accepted declaration, its bindings/local demands, and every generated
child tree even when a child has no successful plan. Keep unsupported scans and
rigid mismatches distinct. Prove that erasing this tree to complete demand plans
is exactly cycle91's compiler and therefore preserves all ordinary models.

Spec 6.3 requires all where children, postpones classification until stable state,
and states that intermediate ambiguity/pending is not an error. The answered
classification boundary in the inbox requires retaining unfinished child results.
This finite static tree implements that retention step, not the stable-state
four-way language classifier. No dictionary is chosen.

## Data, independent judgment, executable path

`Tree α` stores a goal, accepted branches (declaration, bindings, local demands,
all recursively generated children), unsupported declarations, and rigid rejects.
`build registry checked slots sources goal` follows actual accepted captures and
terminates by existing checked Paterson descent. All child lists and duplicates
are retained. The source map has exactly the cycle91 tuple-key alias restriction.

`plans` erases a tree: OR across branches, Cartesian AND across children. The
independent judgment remains cycle91 `Derives`, defined by registry membership,
independent Accepts, original HeadFits, and all-child derivations under one global
source valuation. It is not defined using Tree membership or executable plans.

Principal theorem types (all inputs universally quantified):

- For Checked registry, `plans (build registry checked slots sources goal) =
  CommonRoleGuardedIntervalPlans.compile registry checked slots sources goal`.
- A declaration/capture accepted at the root is retained with its full exact
  recursively built child list, without any child-success/model hypothesis.
- The computed public run has an ordinary-model alternative iff Checked registry
  and there exists one source valuation satisfying old demands and Derives.

## Boundaries and stop condition

Keep existing modules unchanged, add one module and imports/audit/docs. Complete
focused compilation, trust-zero executable boundary checks, axiom audit, diff-only
gate, and work/dots-main publication. General source lowering, occurrence-aware
invocation identity, state materialization/revisits, K2, four-way stable diagnostic
classification, and dictionary observation remain unproved. B4 has five open
major bridges. No new semantic choice is needed for retaining information.
