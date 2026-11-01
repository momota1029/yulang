# Sprint CANONICAL-INFERENCE-MODEL/R194 — fixed mathematical inference instance

Status: admitted continuation of the active Yulang inference goal. R193 was
prepared but never launched; this sprint supersedes its effect-profile lane.
Primary and semantic authority: Luna.

## Original roots and current evidence

Preserve the original four `SourceProblem` roots, source domain and all
quantifiers in `notes/theory/lean/YulangClosure/Contracts.lean`:

1. `InferenceSoundness`: every supported source, actual generated constraint
   object and satisfying assignment gives an original source derivation and
   `sameScoped` for that same assignment.
2. `SourceScopedCoverage`: every original derivation and generated object has
   a satisfying assignment preserving that derivation's scoped witness.
3. `PrincipalCoverage`: one principal solution factors every original source
   derivation through the original `instanceOf` ordering.
4. `InferenceTermination`: the actual inference transition relation is
   accessible from every supported initial state.

Baseline: roots closed `0/4`; R184–R192 discharged `0` premises of those
roots. `SourceProblem` still has abstract `supported`, `sourceJudgment`,
`generates`, `solves`, `sameScoped`, `principal`, `instanceOf`, and transition
fields. Existing structural Simple-sub theorems are conditional components,
not an instance of these fields. Do not report an exact finite count of
unproved leaf assumptions: the concrete semantic instance has not yet fixed
that set.

The R191/R192 backward map identifies the shared first gate: define one
independent canonical mathematical instance of the accepted source language
and Simple-sub algorithm, then state the first source induction step against
those definitions. This sprint constructs that instance; it claims no root
closure.

## Fixed construction target

Define a single coherent Lean model from the accepted authorities and existing
structural definitions. It must expose, with exact constructor equations:

- the full accepted resolved source syntax and its source-local judgments;
- value/effect constraint syntax, generation, accumulation and the actual
  solution/satisfaction relation;
- level-aware propagation, extrusion, intrusion and generalization as the
  selected Simple-sub algorithm;
- annotation permission, actual inflow and handler residual as distinct
  quantities, including symbolic dependencies and residual-constructor
  lineage;
- complete Call and contextual effects wherever the accepted source rules use
  them;
- the original scope, rigid imports, one shared witness, all uses and future
  obligations in `sameScoped`;
- the actual algorithmic transition relation needed later by termination.

Definitions must be independent of the theorem they will establish. In
particular, do not define solving as source typing, define a constraint atom
by its desired `Kernel.atom` result, assume logical admission, assume a
hygienic output, or introduce a permissive primitive standing for a missing
rule. Use the accepted source and inference rules without dropping Call,
effects, annotations, patterns, statements, or supported cases. The model is a
mathematical specification; it does not yet claim that Rust implements it.

If an equation cannot be derived from the accepted authority, stop at that
single original constructor/equation. Record the exact source rule, attempted
equation, owning authority, and the concrete alternatives and consequences.
Do not narrow the source domain or choose a new behavior to make the model
check.

## Root-directed progress graph

```text
fixed canonical model
 ├─ actual generation + independent solution satisfaction
 │    + same-assignment/source-rule induction
 │      → InferenceSoundness
 ├─ original source derivation + actual generation
 │    → solution preserving the same scoped witness
 │      → SourceScopedCoverage
 │        + principal construction + original instance order
 │        + universal factorization → PrincipalCoverage
 └─ exact actual transition relation + well-founded measure
      → InferenceTermination

fixed mathematical model and theorems
  → later Rust generation/propagation/solution simulation
```

These are separate proof obligations. Soundness does not imply coverage,
principality, or termination. Source syntax finiteness does not prove
algorithmic termination. Call and contextual effects remain in the accepted
source domain from the beginning. Rust correspondence follows the mathematical
model and is not its definition.

## Success and falsifiers

Success is one reviewed canonical instance whose every semantic field has an
independent definition and exact accepted owner, whose source constructor
equations cover the complete source domain, and whose solution relation is
neither circular nor permissive. The next proof edges for each of the four
roots must then be stated against this frozen instance.

The parent metric changes only if this canonical prerequisite is accepted or
an original root premise is actually derived. A model containing unresolved
meanings is not a success; root closures remain `0/4` until the original
theorem is proved. Falsifiers include altered source support, missing
constructor equations, an assumed admission, detached scope/witness data,
circular satisfaction, or transitions differing from the accepted algorithm.

## Lane, exact leases, and resources

- One registered `lean_prover` owns only:
  - `notes/theory/lean/YulangClosure/CanonicalInferenceModelR194.lean`
  - `tasks/agent-loop/inbox/canonical-inference-model-r194.md`
- Maximum assignment budget: 2400 seconds. Use the pinned Lean 4.35.0
  project and existing `.lake` only. No new environment/cache/target/scratch,
  Cargo, broad build, or tests. At most one focused `check_lean.py` invocation
  with one CPU, 1 GiB memory, and 240-second timeout if all pinned dependencies
  are already available. Report exact theorem types and complete axiom lists.
- No Rust implementation lane is admitted: the user's phase ordering places
  Rust correspondence after the mathematical model. Existing dirty,
  quarantined, frozen, and question-owned paths remain untouched.
- A fresh independent reviewer, maximum 600 seconds, checks the frozen model
  against every accepted authority, all source constructors, circularity,
  omissions, and the resulting named root edges. The author cannot review it.
- No Astra assignment. Stop on a material semantic choice, missing authority,
  pinned-tool failure, resource exhaustion, or the exact first unsupported
  equation. Report parent delta honestly; do not compensate with auxiliary
  theorem counts.

## Authenticated inputs

The primary freezes exact hashes in the activation receipt before launch.
Required sources are the original `Contracts`, resolved source syntax,
source-directed generation, independent source interpretation/environment,
source checking, the top-level inference principles, selected source
generalization, annotation hygiene, contextual residual lineage, and the
structural Simple-sub constraint/solver/generalization definitions. Additional
inputs require an exact constructor/equation justification and primary
authentication. The previously reviewed R191/R192 parent map is context, not
semantic authority.
