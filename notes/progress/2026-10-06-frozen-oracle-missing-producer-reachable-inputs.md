# Frozen Oracle: inputs reachable before an unannotated formal call

Date: 2026-10-06
Status: compiler-referee reviewed research-only historical characterization; no findings
Claim class: bounded caller/dataflow characterization and conditional branch derivation
Yulang3 baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Check whether omitted **upstream producer inputs** supply a historical source
producer for the ordinary unannotated formal `f` and its `f x` occurrence.
The method is static caller and field-dependency mapping, with an exact
pre-body branch derivation. The earlier endpoint/application and frame
archaeology is retained as input; this lane does not repeat its frame search,
generalization analysis, evaluation-tag mutation, or solver interpretation.

**New mechanism:** ordinary top-level and local parameterized bindings pass
an empty parameter-upper list and no implementation requirement into defined
lambda lowering. Their recursive self endpoint nevertheless causes a
pre-body Function skeleton to be allocated. For an unannotated parameter,
the skeleton installs its shape using the shared parameter endpoint but
**skips its empty-predicate output connections**. The explicit
`KnownBeforeBody` guard makes this distinction. Thus the caller provides
neither a hidden parameter upper that changes `f` to `Annotated` nor an
empty-predicate seed/refinement connection at this pre-body step.

The top-level named-self wrapper does mark its own recursive `apply` binding
`Annotated`. It does not pass that marker to `f`. Source occurrence role/path
metadata is recorded after the application Function demand has been submitted;
the inspected registration routine stores provenance without emitting subtype
constraints. None of these facts establishes the current protected Handler
seed, its ordinary-value refinement, or whole-tuple `U_c`.

This is a bounded stop, not a whole-Oracle absence claim. Historical solver
behavior remains outside the assignment. Any effect/stack interpretation of
these already emitted constraints is still the missing bridge, rather than
an additional explicit upstream producer found here.

## Baseline, authority, and hypotheses

Current authority is [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [nested-block source realization](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3, and the missing-rule interface in
[main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§5. The accepted singleton outcome and exact nested capture meaning remain
fixed. Historical source is evidence only. Source annotations, public types,
internal inferred views, and actual provider roles remain distinct.

Direct historical inputs are the reviewed
[source-producer archaeology](2026-10-06-frozen-oracle-source-producer-archaeology.md)
and research-only
[missing-producer continuation](2026-10-06-frozen-oracle-missing-source-producer-continuation.md).
Neither is used as current language authority.

- H1 (verified provenance): both repository HEADs equal their packet SHAs.
  The fourteen historical files and eight current dependencies listed below
  match their pinned Git blobs byte-for-byte.
- H2 (candidate route premise): the CST of an ordinary parameterized binding
  reaches the inspected ordinary top-level or local binding route; its `f`
  pattern has no `TypeAnn`, its binding has no result annotation, and its
  body lowers successfully. For the nested candidate, the local `step`
  binding reaches that same local route. This lane did not parse, execute, or
  instrument either exact-byte candidate.
- H3 (local derivation premise): before this binding body is lowered, use the
  actual freshly allocated parameter annotation and the fresh
  `initial_frames` supplied by the inspected function, rather than a frame
  already populated by other body calls. The `f` endpoint is distinct from
  the recursive self endpoint. These premises describe the named code step;
  they do not assert that all surrounding solver state is empty.

Established results here are source/blob provenance and assignments/branches
at the named revision. The branch derivation below is conditional on H2/H3.
There is no current source-rule theorem, independent mathematical review,
soundness, principality, source adequacy, or production-conformance closure.

## Exact upstream and downstream map

All following paths are relative to the frozen Oracle tree.

### Ordinary callers supply no hidden parameter annotation

At `crates/infer/src/lowering/body/mod.rs:2184–2232`, ordinary binding dispatch
selects `lower_single_binding_with_context` for a binding with arguments.
That routine allocates a definition root and computes `result_type_expr`
from the binding's own written annotation (`:2280–2293`). It invokes
`lower_binding_body_with_args_to_named_self` for header arguments
(`:2309–2318`). Under H2, the result annotation is absent.

`lower_binding_body_with_args_to_named_self`,
`crates/infer/src/lowering/expr/mod.rs:300–339`, inserts a distinct recursive
self `LocalBinding` whose `call_return_effect` is `Annotated`, then calls
`lower_binding_body_with_args_with_self` with `Some(internal_self_value)`.
That helper, `expr/method_body.rs:56–85`, calls `lower_lambda_params` with
`LambdaScope::Defined`. The marker belongs to recursive `apply`, not to the
parameter subsequently installed from the `f` pattern. No recursive self
call is needed for this machinery to be installed.

For local bindings, `expr/block_local.rs:545–594` allocates the recursive
placeholder and passes `Some(recursive_value)` to
`lower_local_binding_body`. That helper (`:866–897`) reads the argument
patterns/result annotation and calls the same `lower_lambda_params`.

The decisive common call is `expr/lambda.rs:256–268`:

```text
lower_defined_lambda_params(..., self_value,
                           param_uppers = &[],
                           requirement_body = None, ...)
```

Consequently the guards at `:666–673` (submit supplied parameter upper) and
`:690–696` (classify supplied-upper parameter as `Annotated`) are false on
this route. The public helpers accepting nonempty `param_uppers` are not
reached through these ordinary callers. Their method/implementation paths
were only located, not characterized.

Annotation readers are syntactic: `binding_type_expr` reads a header pattern
`TypeAnn` (`crates/infer/src/syntax.rs:297–301`), and `pattern_type_expr`
searches the specified pattern/wrapper (`lowering/expr_syntax.rs:439–456`).
`direct_pattern_type_expr` itself selects `TypeAnn/TypeExpr`
(`syntax.rs:730–738`). With H2, no annotation builder result can insert a
hidden formal annotation at this branch.

### Pre-body skeleton installs shape, but skips the unannotated empty predicate

Defined lowering installs fresh parameter endpoints and frames before the
body (`expr/lambda.rs:664–745`). Under H2, annotation construction returns
empty predicates and `LocalCallReturnEffect::Unannotated` (`:1252–1264`).
The recursive `self_value` makes `skeleton_slots` present (`:747–751`).

`fresh_defined_lambda_skeleton` (`:1127–1144`) allocates function, output and
body slots. `constrain_defined_lambda_skeleton_shape` (`:1146–1174`) submits,
for each parameter `A_f`, a positive Function shape with

```text
arg     = Neg::Var(A_f)
arg_eff = annotation.skeleton_arg_eff
ret_eff = Pos::Var(layer.output_effect)
ret     = Pos::Var(layer.output_value)
```

and connects the outer Function value to the recursive self target. This is
an actual pre-body constraint producer involving `A_f`; it is not merely a
registration marker. Its code contains no explicit callable-role field or
argument-use refinement.

Next, `:756–767` deliberately constructs fresh `initial_frames` and invokes
`connect_defined_lambda_skeleton_predicates(..., KnownBeforeBody, ...)`.
The connection routine (`:1185–1241`) computes each output predicate from
that parameter's annotation and corresponding initial frame. It connects an
empty predicate only if `mode.connects_empty_predicate(param)` is true.
At `lowering/local.rs:138–144`, that guard is precisely

```text
param.annotation.call_return_effect == LocalCallReturnEffect::Annotated.
```

For the unannotated `f` step this is false. In particular, the routine does
not at this step add the empty-predicate edges
`current_effect <: output_effect`, `current_value <: output_value`, and
`output_value <: current_value` found in its annotated branch. This is a
source-level branch fact about emitted constraints, not a denotational
claim about their solutions or about whether other state already connects
those endpoints.

After body lowering, `:788–809` connects the actual body to skeleton body
slots, and `:852–863` builds final parameter wrappers using the frames now
populated by the body. Those later connections are not a second pre-body
interpretation of ordinary-value evidence. Their solver effect and final
public scheme are unverified here.

`ActiveDefinedLambdaSkeleton { before_frames, params }` is pushed at
`:768–772` and truncated after the body. A bounded complete text search of
`crates/infer/src/lowering` found its only read outside setup/cleanup in
`expr/tail.rs:816–821`, the already characterized frame selector. Thus this
metadata supplies a frame-routing input on the inspected lowering subtree,
not an additional observed formal-role predicate. Reads outside that subtree
or analysis of solver state are outside this search claim.

### Name, completion, and occurrence metadata do not provide a prior source predicate

Parameter installation records a separate `Def::Arg` and initially empty
call-state (`lowering/pattern.rs:245–280`). The subsequent input marker writes
`LocalDefRole::Input` in the separate `session.local_defs` table
(`expr/lambda.rs:887–894`). `record_local_completion_scopes`
(`expr/mod.rs:203–255`) stores value/name/source/scope/depth metadata in that
table. The complete inspected name producer reads `LocalBinding`, obtains
its endpoint, resolves its `RefId`, and stores a `RefUse`
(`lowering/name_ref.rs:146–173`); it does not read that table's `role` field.
The application producer likewise reads no `LocalDefRole` field. This
narrows a possible direct metadata input; it does not prove that no later
consumer reads the table.

At `expr/tail.rs:560–563` the application submits its Function demand.
Only afterward, `:564–588` records a `TypeOccurrenceKey` with owner
`Expression(arg.expr)`, role `ExpressionExpected`, and the default
`TypePositionPath`, rooted in the submitted constraint record.
`analysis/session/occurrence_provenance.rs:38–69`, read in full, inserts
fresh-source sets and merges provenance roots/completeness. It emits no
subtype or source-formal constraint. These recorded path/role coordinates
are downstream of this demand's construction. The source-boundary origin
is supplied to the demand earlier; its full solver consequences remain
unverified and are not ruled out by this temporal observation.

## Smallest discriminating derivation and stopping point

For one unannotated parameter in the actual pre-body call:

```text
annotation.predicate.subtracts = []           [lambda.rs:1258]
initial_frame.subtracts = []                  [local.rs:187–194]
initial_frame.latent_subtracts = []            [same]
annotation.call_return_effect = Unannotated   [lambda.rs:1263]
```

`lambda_predicate_subtracts(Defined, annotation, initial_frame)` concatenates
and deduplicates precisely those lists (`expr/tail.rs:1058–1073`), so the
result is empty. `KnownBeforeBody.connects_empty_predicate` is false. The
connection routine therefore follows neither its nonempty predicate branch
nor its guarded empty connection block. The previously emitted Function
shape remains. This rules out the proposed explanation that this particular
pre-body helper supplies an empty-predicate annotated connection for ordinary
`f` through a hidden caller upper or the recursive-self marker.

An analytical control mutation changing only
`call_return_effect` to `Annotated` makes that guard true and selects the
three empty-predicate connection edges, assuming they have not already been
entered under the deduplication key. The mutation distinguishes the branch;
it is not an executed experiment or an accepted-program counterexample, and
is not offered as a current language rule.

The exact blocker is unchanged: an interpretation connecting historical
shared endpoints/effect/stack constraints to current whole-tuple
`U_c(xi; seed, refined, argument, invocation)` has not been established.
The omitted caller/skeleton/metadata routes inspected here do not supply an
explicit additional rule that closes that interpretation. A second endpoint
trace or another stipulated-transition checker would leave this premise
untouched. Recommended next action: define the current minimal-clause §5
whole-tuple predicate from independently source-owned evidence, using this
note only to constrain historical correspondence claims.

## Independence, coverage, checks, and resources

The old source is independent of current research toy models, but its
producer and solver share one historical implementation. It is neither an
independent semantics oracle nor authority for current semantics. Git blob
checks establish provenance only. This producer has not independently
reviewed its artifact.

Commands used: read-only `git rev-parse HEAD` in both trees; bounded `rg -n`
locators/searches and `sed -n` windows; a Python/subprocess byte comparison
against `git show <pinned-SHA>:<path>` plus SHA-256; narrow final artifact
whitespace/path checks. Fifteen frozen-source read/search captures were
used, sequentially. Two exploratory searches named nonexistent `defs.rs`
and `top.rs`; their existing-path matches were retained and the exact
ordinary caller was then located under `body/mod.rs`. An initial combined
current-note capture was truncated; decisive prior-result and main §5
windows were recovered. No absence claim relies on that truncated capture.

Local resource envelope communicated to primary: one sequential lightweight
source process, about twenty-minute wall cap, no builds/tests/execution.
No compiler edit, test, Cargo, formatter, Git mutation, scratch output,
random seed/range, exhaustive program enumeration, executed mutation, or
performance sample was used. CPU, peak RSS, and exact total wall duration
were not instrumented. Current concurrent work was preserved.

Unverified scope: actual CST acceptance/execution stacks; method or
implementation requirement parameter uppers; recursive body calls and
arbitrary aliases; preexisting solver bounds and all solver interpretation;
complete provenance consumers; annotation effect grants; exact current
profile/footprint/admission; soundness, principality, source adequacy and
production conformance. Different source blobs/routes, explicit annotations,
supplied uppers, failed lowering, or non-fresh initial frames invalidate the
corresponding derivation premise. No claim excludes an indirect effect/stack
mechanism implemented by historical solver rules.

## Dependency snapshot

All fourteen directly inspected Oracle files equal their pinned commit blobs.
Newly characterized source files have SHA-256:

| Oracle path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/body/mod.rs` | `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1` |
| `crates/infer/src/lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `crates/infer/src/lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `crates/infer/src/lowering/expr_syntax.rs` | `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` |
| `crates/infer/src/syntax.rs` | `ee305b7659205a4d934c387452380bfc89e05606edc1b44ab732aa82a3b3ee96` |
| `crates/infer/src/analysis/session/occurrence_provenance.rs` | `90613e12e904c74d40894e6f395162c358cc632a8aecb9ddc55db542dd897268` |

Other checked Oracle paths: `lowering/expr/{lambda,block_local,tail}.rs`,
`lowering/{local,pattern,name_ref}.rs`, `uses.rs`, and
`constraints/machine/entry.rs`, all under `crates/infer/src/`.
Their hashes match the frozen prior notes; no dependency changed.
The two governing designs, main minimal-clause note, two prior archaeology
notes, and three required rule files match the current pinned baseline.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-missing-producer-reachable-inputs.md`.
- Baseline SHA: Yulang3 `f93fb06cd40c12fed6caf5051e045f206c4b2da6`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; fourteen historical and eight current
  dependencies matched their pinned blobs.
- Review status: compiler-referee reviewed research-only bounded
  characterization and conditional branch derivation; no findings. No theorem
  closure or implementation authority.
- Checks already run: revision reads; fifteen bounded frozen-source
  read/search captures; source/current blob equality and SHA-256; narrow
  artifact whitespace/path check. No executable/build/test/Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: trace Oracle caller inputs and pre-body skeleton guard`.
- Shared-record deltas intentionally left for primary/curator: record empty
  ordinary-caller parameter uppers; separate annotated recursive self;
  pre-body Function-shape producer with skipped unannotated empty-predicate
  connections; downstream occurrence metadata storage. Retain whole-tuple
  `U_c`, footprint/admission and all proof/implementation gates as open.
