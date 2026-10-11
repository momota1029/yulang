# Top-level mutual recursion: original Value-root reference certificate

Status: Frozen, independently reviewed bounded static characterization; research only
Baseline: `a87a07eed9c9b6e911fd7b2f6ecc0d325d8f1ede`
Branch: `research/simple-sub-intrusion`
Lease: this note only
Method: source ownership and retained identity correspondence; no execution

## Objective and authority

Trace the user's simple top-level mutual recursion through parser, HIR,
collection, and live Value identity. The primary initially assigned
`my f x = g x; my g y = f y`, then selected the existing supported comparison
`my f x = g; my g y = f` as the central witness because its Lambda result
ports directly retain the resolved Name occurrences.

The governing operation is the Authoritative
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, sections “Selected
operation and compiler responsibility” and “Value-reference SCC clarification.”
Vertices are actual Value variables; edges are references in their values.
Comparisons and extrusion ancestry alone are not edges. The reviewed but
non-authoritative `2026-10-11-source-value-reference-intrusion-draft.md`,
sections “Relations that must remain distinct” and “Missing bridge,” supplies
the unresolved full-lifecycle boundary. The Authoritative local-self-recursion
document's “Selected source behavior” excludes local mutual groups; these
examples are module definitions, which use a complete module namespace instead.
The top-level inference principles §§1–3 govern mathematical construction and
proof/implementation direction. No language meaning is selected by this note.

## Established source and identity facts

For the central source:

```yulang
my f x = g; my g y = f
```

1. The parser forms two `BindingStatement`s with headers and bodies
   (`yu-syntax/src/declaration/binding.rs:185–255`). Each has one plain
   parameter and a body identifier. Existing source contracts exercise this
   exact spelling in `yu-solver/src/lib.rs:23072`,
   `tests/shadow_f5.rs:34`, and the extended fresh-use witness in
   `tests/intrusion_transport.rs:1029`. These are inspected test contracts,
   not fresh passing executions.
2. HIR plans all direct-root headers and constructs the complete namespace
   before lowering bodies (`yu-hir/src/module.rs:939–945,1322–1344`). The
   `DefId`s for `f` and `g` differ by spelling, both with same-name ordinal
   zero. Their `DefinitionRootId`s remain artifact-scoped identities.
3. Each parameter gets a `HirParameterId` owned by its definition root
   (`module.rs:1395–1407`). In the candidate source carrier, the outer root
   slot becomes a Lambda and its body is a separate slot
   (`module/local_source.rs:285–322`). Thus `f` owns `Lambda(x, Name(g))`
   and `g` owns `Lambda(y, Name(f))`. There is no nested declaration or
   ownership ambiguity in either initializer.
4. Lexical lookup sees only that function's parameter; the other function's
   spelling resolves through the complete module namespace to
   `LocalSourceResolution::ModuleDef` (`local_source.rs:636–657`). For each
   carrier, expression ordinal zero is the Lambda and ordinal one is the
   body Name. These carrier ordinals do not assert numerical HIR occurrence
   IDs, which are separately artifact allocated by `Builder::set`.
5. `emit_candidate_source` allocates Value/Effect occurrence components,
   emits a pending definition use with the containing definition ordinal,
   resolved target and exact occurrence, then emits `Action::Module`
   (`candidate_source.rs:186–211,376–378`). Collection resolves this into
   `DefinitionUse { parent, target, occurrence, use_value_component,
   target_root_component, ... }` (`lib.rs:1290–1324`). The lexical parent
   and resolved target are retained independently of solver constraints.
6. Every definition root is allocated a `ComponentId::DefinitionValue`
   (`lib.rs:1677–1696,1897–1920`), whose kind is explicitly Value
   (`lib.rs:407–408`). Session startup assigns every Value component one
   distinct dense live Value row before admitting facts
   (`lib.rs:10048–10087`). An occurrence Value row, an Effect row, a
   definition root row, and a parameter row are distinct identity classes
   at that boundary.

Here are exact endpoint locators, without pretending an execution supplied
runtime IDs. Write `df,dg` for the collected definition records and `rf,rg`
for their HIR definition roots; `og,of` are the respective body Names.

| Identity | Exact retained locator |
| --- | --- |
| `F` | `live_components[root_component_positions[rf].component].ordinal`, Value-kind |
| `G` | `live_components[root_component_positions[rg].component].ordinal`, Value-kind |
| `U_g` | `live_components[occurrence_component_positions[og].value].ordinal`, Value-kind |
| `U_f` | `live_components[occurrence_component_positions[of].value].ordinal`, Value-kind |
| Use of `g` | `parent=df`, `target=dg`, `occurrence=og`, `use_value_component=component(U_g)`, `target_root_component=component(G)` |
| Use of `f` | `parent=dg`, `target=df`, `occurrence=of`, `use_value_component=component(U_f)`, `target_root_component=component(F)` |

The parent root component is obtained directly through
`definitions[record.parent.ordinal()].root` and `root_component_positions`;
its absence as a redundant field in `DefinitionUse` is not missing evidence.

## Bounded derivation and its exact boundary

At the original module-root boundary, use the fixed source-reference meaning:
a Name occurring in a definition's own initializer value is a reference from
that value's owning Value root to the resolved definition's Value root.
These roots are the actual distinct collected/live Value variables established
above. This is the selected reference interpretation, not a reinterpretation
of a subtype judgment.

The `Name(g)` occurrence belongs to the value of `f`, resolves to `g`, and
its retained `DefinitionUse` supplies both definition identities. Composing
those identities with the injective initial Value-root allocation yields
`F → G`. Symmetrically, `Name(f)` yields `G → F`. Therefore the two original
Value roots lie in one nontrivial SCC of that source-qualified reference
relation. In any larger graph retaining these edges they remain mutually
reachable; this does not claim their maximal SCC has only two vertices.
This certificate is grounded in source construction and root allocation,
without deriving adjacency from `SccPlan` membership or comparison direction.

The definition dependency graph independently has exactly the component
`{df,dg}`: `SccPlan` consumes the retained `DefinitionUse` records, with
parent/target ordinals (`scc.rs:817–819`). That planning fact is corroborating
source scheduling evidence, not the premise of the Value-root derivation.

The stronger expanded paths `F → U_g → G` and `G → U_f → F` are **not
established here**. Occurrence rows are separate vertices. To call these exact
arrows semantic reference edges requires a stated constructor rule assigning
occurrence facades to owned values and retaining their Name references.
The direct root certificate does not force that particular factorization.

The ordinary route preserves the native endpoints: candidate SCC scheduling
registers all member roots and internal uses before executing either body
(`candidate_scheme.rs:868–886`); open module use validates both active
definitions and calls `route_internal` (`:938–945`). The latter constrains
`G <: U_g` or `F <: U_f` (`lib.rs:15760–15782`). These comparisons are
operational facts; they do not independently prove either expanded reference
edge or an equality of occurrence and root identities.

For the candidate source carrier, each `LambdaRecipe` retains its Name body
endpoint (`candidate_source.rs:445–459`); `admit_lambda_fact` constructs a
positive Function whose result port is that endpoint
(`lib.rs:11249–11262,11340–11362`). The source root is linked to its Lambda
expression component by `Action::Link` (`candidate_source.rs:477–494,665–668`).
These constructors give concrete owners for further correspondence work, but
no automatic converse from stored lower/upper incidence is used here.

## Requested application form

For `my f x = g x; my g y = f y`, whitespace application is admitted as
`MlArgument` (`yu-syntax/src/expression/operator_chain.rs:758–818`). The
candidate HIR carrier forms `Apply(callee, argument)`
(`local_source.rs:527–568`). Per definition its slots are Lambda zero,
Apply one, callee Name two, argument Name three. Callee Names resolve to the
other module definition; argument Names resolve to their own parameters.
At source ownership granularity the references are `f → g`, `f → x`,
`g → f`, and `g → y`; the two module references again supply the direct
original-root certificate. Acceptance/inference of this exact application
source was not executed, and the inspected supported return-form tests do
not establish that execution result.

An expanded Value-constructor argument must additionally address Apply:
`LambdaRecipe` uses the Apply **result** endpoint, while
`CandidateRelation::Apply` separately retains its **callee** endpoint
(`candidate_source.rs:394–410,445–459`). Admission constructs a negative
Function demand with argument/result ports and constrains the callee against
it (`shadow_apply.rs:1331–1399`). There is no callee port in the Lambda's
positive Function constructor. This distinguishes the two sources without
proving that a semantic callee reference is absent: its source-owned reference
is present, while a proposed expanded path through the Apply result needs its
own retained-reference construction/transport rule.

## Intrusion consumer and remaining gates

`settle_candidate_intrusion` constructs its graph from direct lower/upper rows,
nonvariable bounds, Function ports, and Effect endpoints
(`candidate_intrusion.rs:375–475`). The inspected graph build does not consume
the source ownership/parent/target certificate above. It may skip graph work
when there are no retained extrusion parents (`:370–373`). This note proves
neither equivalence nor inequivalence of that operational graph to the selected
Value-reference relation. Equivalence would need a correspondence argument for
each included/omitted reference, not a successful dependency-SCC calculation.

The displayed roots are two distinct module definition roots, not a witnessed
extrusion parent/copy pair. No parent/copy co-membership, copy-edge ownership,
fresh-use transport, generalization transport, intrusion adequacy, soundness,
principality, complete Call, or production gate is closed.

Recommended next action: hand the direct original-root certificate to the
assigned prover/source correspondence owner, and require its extension to the
actual reference construction for extrusion-created identities and the
intrusion consumer. Preserve the supported return source as the smallest
existing two-definition witness; do not repeat a payload-only SCC probe.

## Checks, dependencies, and resources

Checks were static `rg`/`sed` source reads, `git show` authority reads,
`git ls-tree` dependency identity inspection, and read-only
`git diff --name-only <baseline> -- <exact inspected paths>`. That scoped diff
was empty before writing this artifact; HEAD equaled the pinned baseline.
No tests, builds, Oracle runs, solver instrumentation, exhaustive search,
mutations, or children ran. No independent oracle is claimed: the source and
implementation evidence share the fixed graph meaning and source ownership
premise; inspected test contracts are not execution or independent proof.
Seeds/ranges and executable coverage are not applicable. Static coverage is
the two displayed module sources and named collector/constructor/route owners.
At most three lightweight shell/read processes ran concurrently within this
lane; peak RAM/CPU and exact aggregate wall time were not measured. No heavy
computation was started.

The core frozen Git blob identities are:

```text
module.rs              8231ff7dd4461dec455de594b1b84ad070ac76c0
module/local_source.rs cc0f08da32b8cf3884597c53dee8d74d474f3bed
candidate_source.rs    632fb512ea8086ea8ed2065997ad619d582576ee
candidate_scheme.rs    a774de6f69f5177014bec22c2db0bdf904d0a7b8
lib.rs                 a436989febc4e9a3203af0552332821859857709
shadow_apply.rs        04b9c4a340ed2bf2ec6a58b81311958dae173513
scc.rs                 945baf7dc2d59e74616f549f28703ef7a84f5eed
candidate_intrusion.rs d2c444e7d369fb10ec8ba3c2d94a385b219e38ab
```

Failure/invalidation conditions: changed module resolution or value ownership,
noninjective initial root allocation, changed collection parent/target mapping,
or treating fresh/copied identities as already covered by this root-only
certificate. Unrelated working-tree artifacts were preserved. Independent
compiler-referee review accepted the bounded original-root result only.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-mutual-recursive-value-scc-source-trace.md`.
- Baseline SHA: `a87a07eed9c9b6e911fd7b2f6ecc0d325d8f1ede`.
- Changed dependency hashes: none observed; direct dependencies matched baseline.
- Claim/review status: frozen independently reviewed bounded original-root construction
  certificate; expanded occurrence paths and lifecycle/consumer gates OPEN.
- Checks already run: named static reads and read-only baseline/path equality;
  no executable checks, tests or builds.
- Proposed commit message: `research: trace mutual module references to original Value roots`.
- Shared-record deltas left for primary/curator: record the original-root
  two-cycle certificate and narrower remaining copy/consumer bridge; no theorem
  or production promotion. No shared task/index/authority/question file changed.
