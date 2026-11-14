# Total materialization of the current WF declaration language

Status: constructive equation compiler and coverage proofs; operational consumer migration remains open. This note does not establish a successor boundary or transfer its twelve laws. The previous WF boundary and its twelve proofs remain unchanged.

## 1. Exhaustive syntax inventory

The relevant grammar is `GeneralDeclarationPatterns.Pattern`, not the entire Yulang surface grammar. It has **exactly five constructors**. Associated equations and named where requests contain arbitrary `Pattern`s; the head/unnamed-input counting checks do not restrict their RHSs to the inspection fragment.

| Pattern constructor | Forms represented | Existing inspection/materialization | Successor equation expression |
| --- | --- | --- | --- |
| `var name` | Shared impl variables, including output-only variables | Variable capture; actual mode uses the explicit center in centered semantics | Input binders in actual mode and corresponding endpoints in lower/upper mode; output-only binders in every mode |
| `app key arguments` | Resolved primitive or nominal constructor, arbitrary syntactic arity | Scalars, binary pair, empty record, exact empty record; invariant nominals with all-type parameters and correct arity; other applications defer | The same four primitive families and all-type invariant nominals, checked against the WF metadata and arity |
| `record label payload tail` | Required fields, closed record spines, arbitrary open/nested tails | Only tails translating to a closed record node work; open or non-record-query tails defer | Ordinary carrier `record label payload tail`, with no restriction on the evaluated tail |
| `variant tag payload` | A tag with any payload, including payload unions | Structural node; `plainNames` turns a payload made of joined variables into simultaneous captures | Ordinary carrier `variant tag payload`; a joined payload denotes a union |
| `join first last` | Multi-tag variant rows, duplicate-tag payload unions, other unions in the formal grammar | Residual joins defer, except inside the preceding `plainNames` shortcut | Ordinary carrier union, recursively at any depth |

Application cases are exhaustive over `Primitive`: `scalar base` (zero arguments), `pair` (two), `emptyRecord` (zero), `exactEmpty` (zero). A tuple already represented by nested pairs is covered. A nominal has its resolved catalogue name and a finite list of actual type arguments; its body is not unfolded. Nominal arguments switch to actual mode even inside a lower/upper request, as in the existing centered materializer.

`Roles.Term`, used for defaults, has exactly `var` and `app`. Defaults use **positional role input centers**, not impl capture variables and not the `Pattern.encode` numbering used by counting. The successor default compiler uses the same resolved constructor metadata as explicit bodies.

Scope boundaries are material:

* `Pattern` has no dedicated function, effect-row, intersection, top/bottom, optional-field, record-default, recursive-type, or quantified-type constructor. The current primitive interpretation has none of those constructors either. They may occur as already interpreted values behind variables. A general `app` could name an elaborated form, but its constructor meaning must be supplied by an enlarged interpretation before it is a WF source of this boundary.
* Catalogue parameters can syntactically be `.type`, `.row`, `.lower`, or `.upper`. The existing `HeadWF.ConstructorUse` accepts primitive layouts or all-`.type` invariant nominal layouts. It excludes other layouts. The new completeness theorem does not silently expand that source contract.
* Thus the theorem is exhaustive for **every constructor of the current WF Pattern/Term fragment**, not a parser-to-Lean theorem covering all source-language function/effect/default forms. The carrier already has function and row operations; their source metadata/elaboration bridge is separate, not an unresolved meaning for outputs.

The governing decisions already settle the forms being added. Spec §4.3 says “隠れた field は、型の上でも無かったことになる”; direct carrier records have that behavior (`record_shadow`). Spec §4.5 says “tag は一意で、payload は tag ごとに合流する”; carrier unions satisfy it (`duplicate_tag_value`). Spec §4.7b distinguishes variant-row syntax from ordinary union annotation; this work introduces no new surface annotation. Spec §6.3 requires the ordinary equation `'v = value` after selection and an error if it conflicts with accumulated constraints. Spec §6.1 permits omission of an associated body when its role supplies a default. No new pending rule or owner decision is needed here.

## 2. Compiler, equations, and completeness

The new modules use the prefix `GeneralNominalCenteredHeadMat`:

* `Expressions`: `translate` and `translateDefault` recursively compile to `Expr`; `application` checks constructor presence, layout and arity. `value` evaluates over `CommonNominalFullCarrier.Ty`. `translate_complete` and `translateDefault_complete` cover every WF input. An unsuccessful compilation records an invalid/uncovered input; it is impossible under these theorem premises.
* `Schemas`: one request becomes one equation between its target and the full evaluated expression. `Equation.Holds` is precisely the conjunction of the two ordinary carrier subtype constraints (`ordinary_equations`). `unknown` records failed compilation; it is not cleared independently of translation. `generated_contains` and `generated_equation` prove that successfully translated requests are retained and enforced.
* `Plans`: `emittedSchema` and `childSchema` compile source RHSs and actual child-center requests. The prospective `Models` replaces the old named/input schemas, retaining head equations, center bounds and child bounds. `generation_certificate` is relative to these new plan models; it is not a proof of their existence or an operational support theorem.
* `Effects`: every merged-class output request uses explicit-first associated lookup, falling back to the role default. `Ready` has no default deferral. `ClassEffects` enforces every successfully looked-up body and `EqualOutputs`, including requests present on only one alias occurrence. `Ready` supplies the lookup coverage. `ready_of_wf` eliminates both explicit-body and default translation coverage obligations, retaining the named `RequestsDeclared` premise.

Emission compiles **the original source patterns** retained by `emit`. It does not pass them through the head-inspection language or use counting normalization as an evaluator. Hidden fields and duplicate tags have their ordinary semantic equalities in the carrier. Every emitted input contributes lower and upper equations, including bare-variable self-equalities; every named output contributes its actual-mode equation. Actual child centers also have equations for their whole source patterns.

The main coverage statements are:

```lean
GeneralNominalCenteredHeadMatSchemas.wf_emitted_schema_complete
  (covered : Coverage registry interpretation)
  (visible : declaration ∈ registry.declarations)
  (checked : DeclarationChecked registry.constructors roles declaration) :
  (generated registry.constructors interpretation
    (requests state registry root declaration checked bindings)).unknown = false

GeneralNominalCenteredHeadMatPlans.reachable_emitted_complete
  (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles)
    registry root state)
  (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
  (emittedSchema plan).unknown = false
```

The second theorem uses the existing WF reachability invariant to supply the first theorem's metadata. `reachable_child_complete` covers every recorded where clause's actual center schema as well. There is no assumption that the RHS is inspection-supported, normalized to a closed record, or free of joins.

## 3. Model extension and fixtures

`Extension.extend` explicitly assigns each equation target its RHS value in the previous assignment. `extend_holds` proves all equations when targets are distinct and no RHS source is one of those targets (`Independent`, quantified over every mode). `source_model_extension` additionally assumes targets are fresh from `GeneralNominalState.sources` and preserves the original raw source model. `common_model_extension` instead names the remaining journal-preservation premise: every assignment agreeing outside these targets preserves the previous journal model. Neither theorem assumes that the desired extension already exists.

These conditions are sufficient, not established for every prospective reachable packet. Repeated targets and dependencies between allocated centers need a more general construction or equality/coherence analysis; old targets carrying output requests need the selected branch's consistency argument.

`Examples.row_emission_complete` closes the previous two-tag fixture's schema blocker. `Examples.Rows.source_extension` constructs a model of its complete emitted schema while preserving its source model. `Examples.Defaults.ready` and `Examples.Defaults.inhabited` prove complete positional-default effects with a common existing pre-state witness. These are equation/model results, **not installation traces**; the old Step still consumes the old schemas.

## 4. Why the operational wiring is not a ledger-only extension

Head capture and output construction have different operations. Spec §6.3 says that the plain variables in a repeated-tag **head** both capture the merged payload. That is why inspection legitimately uses `plainNames`. Output construction must instead substitute the already captured values and merge their payloads.

For example, after capturing `'a = int` and `'b = bool`, a named output with source RHS `:{tick 'a, tick 'b}` denotes `:tick (int | bool)`. Consider a binary `P 'a 'b` impl with a zero-input `Q(out = :{tick 'a, tick 'b})` where child. This is a schematic declaration illustrating the distinction, not a new compiled trace fixture.

The existing normalized output translator produces a single payload origin with `.variables [a,b]`. `Examples.legacy_requires_equal` proves that its centered schema forces the two binder values to be equivalent. Conversely, `Examples.union_does_not_require_equal` constructs an inhabited model of the new ordinary union equation with distinct `int` and `bool` inputs. `Examples.distinct_inputs` proves their inequivalence in the full carrier. Consequently a generic implication from the corrected output equation to the retained simultaneous-capture equation cannot be used as a migration strategy. These are model-level facts, not a second reachable-counterexample claim.

The old constraints are consumed in all of the following places:

1. `GeneralNominalSaturationState.Packet.Holds` / recursive branch models and `GeneralNominalCenters.Plan.Equations` include the old materialization semantics.
2. `GeneralNominalCenteredSupport.Outputs`, output certificates/readback and trusted output promotion use the same old schemas. Replacing only the install `unknown` guard would retain their incorrect equality constraint.
3. `GeneralNominalCenteredSteps.Models`, raw saturation models and the head-step effect ledger quantify over those packet/plan meanings.
4. Refresh and administrative semantic certificates quantify over the old model class. `CenteredSteps.Refresh.exact` specifically assumes old centered models. Dropping an old output constraint can enlarge that class, so its old certificate does not automatically prove the corresponding fact for corrected models. The existing refresh definition and behavior have not been changed.

The exact remaining bridge is a coherent replacement of these output equation producers **and consumers**, with model-restriction and observation/readback proofs for the resulting journal. A retained refresh certificate requires proof of its entailment over the corrected model class; no such transport is supplied here. This is an implementation proof obligation, not a proposal for new language laziness or a claim that the refresh owner question has been answered.

## 5. Boundary and law status

There is deliberately no boundary wrapper presented as operationally repaired. The existing WF boundary's twelve laws still hold for its existing Step and models. None has been relabeled as a law of a new materialization Step.

| Existing law | Work needed for a successor using the corrected journal |
| --- | --- |
| `stepModels` | Reprove packet/effect model restriction and all administrative/refresh certificate consumers over the corrected journal |
| `closure` | Reuse the generated-focus `Step`/`Stable` argument once the successor constructors are defined |
| `progress` | Instantiate the ground finite-cover argument with the corrected retrospective model and readback invariants |
| `execution`, `halted` | Derive from successor accessibility and its executor transport |
| `frontierLocal`, `localIdentity` | Rebuild the choice frontier using successor effects/conflicts; generic V6 functionality remains available |
| `whereAccessible` | Reuse head-survivor Paterson descent, with the successor Local-to-survivor projection |
| `treeExecution` | Rebuild the executor's final resolver identity for the successor Local |
| `dictionaryRefl` | The dictionary equivalence relation itself is unchanged |
| `initialReorders` | Source coverage reordering is unchanged; connect it to the successor initial state |
| `canonicalLocalOrder` | Extend the existing packet/plan correspondence to total expressions, positional defaults, corrected journals and their consumers |

`GeneratedChildren` and the old availability `Extension` are not closed. Their remaining mathematical premises include fresh/coherent allocation for all new equations, journal preservation under their assignment, compatible center choices, corrected raw value support/readback, and a common successor model. `RequestsDeclared` for every live alias class is also not discharged by the new coverage theorem. `EvidenceNode` remains outside this worker's scope.

## 6. Checks and proof provenance

The primary constructed these bounded proofs; no registered `prover` role or launch surface was available. Separate reviewers inspected source/consumer ownership and all six modules. The final module review found no source defect; its two documentation qualifications are incorporated above. The new audit prints all 57 public theorem dependencies, whose union is exactly `propext`, `Classical.choice`, `Quot.sound`.

Final commands, from `lean/` (each exit **0**):

```sh
lake build --wfail Yulang.GeneralNominalCenteredHeadMatExpressions Yulang.GeneralNominalCenteredHeadMatSchemas Yulang.GeneralNominalCenteredHeadMatEffects Yulang.GeneralNominalCenteredHeadMatPlans Yulang.GeneralNominalCenteredHeadMatExtension Yulang.GeneralNominalCenteredHeadMatExamples > /tmp/centered20-modules.log 2>&1
lake build --wfail > /tmp/centered20-build.log 2>&1
lake build Yulang > /tmp/centered20-yulang.log 2>&1
lake env lean Audit/GeneralNominalCenteredHeadMat.lean > /tmp/centered20-audit.log 2>&1
```

`git diff --check` and the check that the two existing-file changes are strict suffix additions also exited **0**. Iterative elaboration failures were corrected before these final checks. No references or commits were changed. The exhaustive theorem-name list is in `lean/Audit/GeneralNominalCenteredHeadMat.lean`; the nontrivial remaining premises and the unimplemented operational bridge are listed in §§2–5 above.
