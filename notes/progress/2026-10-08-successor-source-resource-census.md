# Source to inference artifact census

Date: 2026-10-08
Baseline: `a38551e9525bf8f079a9ced24f312282c934b46d`
Branch: `research/simple-sub-intrusion`
Claim class: performance-auditor-reviewed bounded static characterization and
conditional counting derivation. No performance measurement, source
Generalize theorem, semantic adoption, or Gate D closure.

## Objective and governing boundary

Join real source construction to countable artifacts upstream of the existing
[structural resource audit](2026-10-08-successor-structural-resource-audit.md).
This note counts source recipes and their emitted or retained records. It does
not repeat the downstream SCC, replay, lifetime, or failure-cost audit.

Governing sections are design-authority **Authority order** and **User-selected
product priorities**; performance **Measurement decision**; the authoritative
F5 foundation §§3–5, 7–9, 12, 14 and 21; inferred-call-views §§2 and 5; and the
successor charter Gate D, Gate E and §12. The charter's research status is not
implementation approval. Its §12 permits a future named successor complexity
boundary without selecting one. The authoritative F5c no-numeric-cap addendum
§§1–3 takes precedence within current F5c: these counts do not authorize a
source-size, work, or time cutoff there.

The pending `successor-generalize-root-policy/q1` question is a read-only
dependency. Neither retained-root nor transformed/common-root export is assumed.
Current task/index changes supply navigation only. The user objective remains
completion of inference and replacement of F5.

## 1. Exact startup census for the ordinary source path

Hypotheses: successful ordinary `lower_module` followed by
`ConstraintBatch::collect`, with `candidate_values=false`; no synthetic test
extension and no alternate shadow candidate collector. Count the records the
current collector actually emits, including roots whose bodies are erroneous.
This is the narrow F5 recipe, not all intended successor source syntax.

Let:

| Symbol | Source/HIR incidence counted |
| --- | --- |
| `D` | Registered `HirItem::Binding` roots |
| `P` | Root Lambda parameters appended to `parameter_recipes`, including unsupported/error bodies |
| `L` | Supported root Lambdas appended to `lambda_recipes` |
| `L_p` | Those `L` whose body is the same parameter Name |
| `I` | Integers processed by `emit_integer`, including supported Lambda bodies and standalone integer expressions |
| `I_r` | Those `I` emitted with a direct definition root |
| `J` | Resolved module Names processed by `emit_resolved_binding_name`, at binding bodies or supported Lambda bodies |
| `J_r` | Those `J` emitted with a direct definition root |

Owning constructors are `yu-hir/src/module.rs::next_occurrence` and the
binding lowering that wraps one admitted parameter's body in `ResolvedExpr::Lambda`;
then `yu-solver/src/lib.rs::ConstraintBatch::collect_mode`,
`add_definition_root`, `emit_integer`, `emit_resolved_binding_name`, and
`emit_lambda` (`:859`, `:1591`, `:1614`, `:1673`, `:1717` at this baseline).
The Name lookup result distinguishes parameter references from module uses.

Direct inspection gives these **exact logical counts**, rather than samples:

```text
value components          = D + I + J
effect components         = I + J + L_p + L
startup live value rows V0 = D + I + J + P
startup live effect rows  = I + J + L_p + L
collected occurrences A0  = 4I + I_r + 2J + J_r + 2L_p + 2L
deferred Function recipes = L
retained module uses U    = J <= D
```

Derivation: each root allocates one value component; each emitted Integer or
module Name allocates one value/effect pair. A parameter body allocates only
an effect component and reuses its parameter value row. Each supported Lambda
allocates one further effect component. Integers emit four leaf constraints,
plus one when attached directly to a root; module Names emit two effect
constraints, plus one at a direct root. Parameter bodies and Lambdas each
emit two effect constraints. `InferenceSession::try_new` (`:9402`, `:9718`)
allocates one live row per component and appends `P` parameter value rows.
`admit_lambda_fact` (`:10790`) creates one Function-to-root fact per recipe.
Each `J` queues and resolves exactly one `DefinitionUse`; ordinary supported
binding bodies contain at most one such module Name. No parameter reference
becomes a `DefinitionUse`.

Thus source admission attempts are `A0 + L`, followed by at most `U` top-level
use-route fact attempts; an incoming Bottom route retains no fact. This is
not a count of derived bound restorations, pair decompositions, or explanation
edges. Each admitted fact can have multiple provenance causes.

If `S = D + P + I + J + L`, startup rows, recipes, direct-fact attempts and
their fixed-arity endpoint construction are `O(S)`. The source seed graph's
constructor attempts have `O(S)` nodes/operand incidences; interned node
counts may be smaller. Source identity/spelling/module-path payload bytes are
a separate dimension. No parser/CST-node-to-byte theorem is claimed here.

Two discriminating source traces, derived without running the compiler:

| Source | `D,P,I,J,L,L_p` | Startup value/effect rows | `A0`; deferred Function facts |
| --- | --- | --- | --- |
| `my id x = x` | `1,1,0,0,1,1` | `2 / 2` | `4`; `1` |
| `my k x = 1` | `1,1,1,0,1,0` | `3 / 2` | `6`; `1` |

The identity has no body value row or parameter-to-body equality fact. The
constant has an Integer result row and its two value facts. Replacing an
admitted Lambda body by unsupported/error content can leave `P=1` while
`L=0`; counting only successful Functions would miss that startup parameter
row. These traces discriminate emitter ownership, not semantic eligibility.

## 2. Uses supply a weighted binder census, not an output-size theorem

`component_generalization_draft` (`lib.rs:15475`) selects the member's exact
startup root row and invokes `F5cGeneralizer`. In
`f5c_generalization.rs:11029`, Q selection maps retained bipolar eligible
value-row ordinals; R selection maps distinct retained recursive owners and
excludes those owners from Q. The implemented eligibility test (`:11603`)
uses current row level and non-generic closure. A source `HirParameterId` is
therefore not automatically a Q binder, R binder, or successor eligible identity.
The frozen private HIR `EvaluationClass` is also not a completed successor
eligibility certificate.

For a successfully exported current scheme `b`, write
`k_b = Q_b + R_b` and `V_b` for live value rows available when it is drafted.
The disjoint maps keyed by actual row ordinal give the structural inequality
`k_b <= V_b`. The shadow origin capture (`:11774`) stores exactly `k_b`
scheme-qualified `(kind,binder,row)` entries when requested; counting distinct
historical rows across schemes would lose this multiplicity.

For successful ordinary incoming uses, let `U_s` be the routes entering the
structured branch of `route_incoming_inner`. The exact fresh-row count is:

```text
F = sum over u in U_s of k_target(u)
final live value rows = V0 + F
```

`instantiate_and_route_closed_inner` (`lib.rs:14796`) allocates one value row
per Q and R, using a single substitution map; internal SCC uses allocate none.
`route_incoming_inner` (`:15162`) takes Bottom and Int paths without fresh
binders. The production-region call-site search finds no other calls to
`fresh_value_at_level` and no calls to `fresh_effect_at_level`. The successful
ordinary path therefore retains the startup effect-row count above. These
equalities exclude alternate candidate construction and failed attempts.

A coarse conditional source bound follows: after incoming route `i`, its target
scheme was drafted earlier, so `k_target(i) <= V_(i-1)`. Consequently
`V_i <= 2 V_(i-1)` and `V_final <= V0 * 2^U`. This is a deliberately loose
bound on **rows only**, conditional on successful ordinary source execution
and the cited distinct-row selection invariant. It proves no exponential
lower bound, no useful ordinary-family performance guarantee, and no bound
on expansion work, structured term nodes, evidence, or output bytes.

The source seed `O(S)` graph must consequently remain distinct from the later
inference graph. `VariableBounds` and `EffectBounds` retain direct row edges
and exact non-variable memberships (`lib.rs:3866`); no inspected source
emitter enumerates the eventual derived incidences. This census supplies
initial counts and the fresh-use multiplier, not a linear end-to-end `N/E`
claim.

Existing workload declarations provide a narrow executable bridge for a future
verification owner, without adding evidence from a run here. In
`crates/yu-solver/src/tests/f5c_resource_probe.rs`, `matrix_source` (`:1404`)
builds real independent identity and identity-alias source strings.
`matrix_identity` (`:2143`) asserts `2D` startup value rows, `2D` effect rows,
`5D` source facts and `D` Q writes; `matrix_aliases` (`:2161`) asserts `U`
incoming fresh value rows and `5U` closed-node visits for that specific source
family. `source_lambda_cases` (`:403`) includes real productive source rings
at `2/4/8/16` members. These are inspected harness assertions, not observations
or proofs of larger sizes. Manually seeded depth/width cases are a different
input class. Probe-only/ignored `1000/2000/4000` declarations are no completed
measurements. The F5c addendum §§4–5 governs any new measurement plan and keeps
its policy-cap exception confined to F5c.

## 3. Which evidence, views and outputs are actually emitted

| Artifact | Owning constructor/representation | Source join and limit |
| --- | --- | --- |
| Direct facts and causes | `ConstraintOccurrenceId(occurrence,local_slot)`, `CauseId`, `ConstraintStore::admit_and_record_provenance` | `A0+L` source attempts are counted above; derived provenance volume is not supplied by that count. |
| Current scheme output | `GeneralizationDraft`; `ClosedTypeFinalizationSession`; `ClosedValueScheme` and `ClosedTypeArena` in `yu-types/src/lib.rs:630,731` | One successful scheme header per `D`; its predicate DAG, child spans, recursive bounds and finalized node count require the generalizer result. A header count does not bound exported graph or serialization size. |
| Current generalization/fresh-use observations | `shadow_f5.rs::GeneralizationOriginRef`, `FreshInstantiationRef`, `ClosedSchemeRef` | Borrowed current-solve identities; origin/substitution entry counts are `k_b`/`k_target(u)`. A borrowed `ClosedValueSchemeView` is not a source semantic call view. |
| Retained call inventory | `HirModule::shadow_resolved_call_inventory` in `yu-hir/src/shadow.rs:160` | On successful selected-root projection, exactly one record per traversed retained HIR Apply; absent source calls and unsupported projections have no completeness guarantee. |
| Pending call carriers | `yu-core/src/shadow_call_formation.rs::generate_resolved_source_calls`, `generate_source_calls` | The first maps supplied retained calls one for one; the second maps retained resolved source-call incidences after the declaration filter. Records keep unresolved premises. They supply no complete typing/admission evidence or Generalize judgment. |
| Captured symbolic Gen-Call-0 | `generate_captured_declaration` / `generate_captured_from_skeleton` (`:298,309`) | Exactly zero or one symbolic record for the supported captured-call declaration. This does not count all-source semantic Gen-Call-0 records. |
| Source semantic view | `SourceViewPremiseLocator` (`yu-hir/src/shadow.rs:1314`) | Locates inputs and explicitly constructs no `SourceViewInst`, typed Flow, receipt, receiver, world admission or Q result. No source-view emission count follows. |

Complete source evidence is not the number of pending-premise enum categories.
Likewise the finite production Option 2 grammar is not a list of runtime
histories/observations to enumerate per source use.

The precise missing join is the **actual source Generalize constructor**
`g_b`: selected whole view and designated endpoint, eligible identities versus
fixed transitive captures/imports, original binder scopes, and complete
comparison-independent membership/admission evidence. PG-1 direct evidence
§§3–4 supplies a conditional aligned whole-root certificate; the export
constructor candidate §§3–5 takes `g_b`, the finite joint presentation and its
indexes as inputs. Its packing bound does not bound their source construction.
There is also no complete source emitter for all semantic view/admission
records from which to derive their multiplicity. The pending root-policy
choice blocks specifying the first designated export; source eligibility and
complete evidence remain separate missing premises under either option.

## Evidence discipline, snapshot and next action

Independent performance-auditor review found no blocking, major, or minor
finding in the stated equations, row bound, fixture descriptions, or scoped
F5c resource authority. The review did not certify successor semantics, the
shadow-carrier/view inventory, or downstream materialization and failure paths.

Method: direct source inspection with bounded `rg`, `sed`, `cat`, read-only Git
status/revision/diff and SHA-256 dependency checks. The startup equations are
constructor-case derivations from actual Rust bodies, not a checker with
assumed transition rules. No oracle was executed; semantic oracle independence
is not claimed. Code and F5 contracts share the selected current architecture,
so their agreement cannot certify successor semantics. No seeds, sampled
ranges, mutations, benchmarks, builds, tests or compiler executions were used.
Shell inspection was sequential; CPU/RSS and precise wall time were not
measured. No heavyweight process was launched.

Coverage: ordinary collector/startup, current Q/R selection, fresh allocation
call sites, the named shadow call emitters, and current closed representations.
Omitted: parser-wide scaling, every normalization/materialization route,
semantic eligibility, exhaustive evidence formation, all successor views,
transformed export, serialization, and failures' allocation histories. No
global complexity search or exhaustive compiler audit was performed.

The inspected implementation and direct governing/previous-result dependencies
match the pinned baseline. Unrelated task/index/architecture/theory edits were
present and remain read-only; none is a premise of these equations. The pending
question is untracked and its exact inspected SHA-256 is
`69f43d833a0237523c88a26125f3cf4878e599e38903f84b458d437da662072b`.

Recommended next action: when the primary has the approved first export target,
make its source Generalize proposal retain an explicit census of emitted whole
view, binder/fixed-closure and evidence records at their owning constructors.
Use the equations above as current-source input counts; prove their successor
record multiplier before scheduling resource measurements.

## Commit packet

- Exact lease: `notes/progress/2026-10-08-successor-source-resource-census.md`.
- Baseline: `a38551e9525bf8f079a9ced24f312282c934b46d`.
- Changed dependency hashes: none among directly used tracked implementation,
  governing sources and prior-result notes; pending question hash recorded above.
- Review: performance-auditor review clean in the bounded characterization
  scope; no gate/status promotion.
- Checks already run: narrow source reads, allocation call-site search, direct
  dependency diff/hash checks, leased-path whitespace check; no executable check.
- Proposed commit: `research: derive source recipe counts and pin successor census seam`.
- Shared deltas left to primary/curator: link this upstream census from the
  structural resource audit or Gate D ledger after adjudication; retain missing
  source Generalize/evidence/view formation and output bounds as open. No shared
  task, index, design authority, theory ledger or question bundle was edited.
