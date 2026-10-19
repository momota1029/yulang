# R139: finite correspondence for two curated diagnostic examples

Status: candidate source/native evidence; independent final review pending.
Author: `/root/r139_proof`; no contributing descendants.
Contract: `tasks/agent-loop/sprints/yulang2-diagnostic-examples-20261020-r139-rev4.md`, revision 4, SHA-256 `3c799b9f735de41ea8a033ad6b5d9920e296a0bc19e5b907159009f7cfadc47f`.
Baseline: `0e7a71b23b86390390e608282b217ef354930e86`.

## Claim, domain and evidence boundary

The finite obligation is the contract's Source-to-proof obligation, for exactly
the two unchanged templates below, through the ordinary experimental candidate
path (`scoped = false`). The result identifies the actual source constructors,
generated constraints, copy/propagation owners, incompatible primitive comparison,
and preparation barrier. It supplies a static explanation of the required
candidate-conflict outcome. It does not certify a general source rejection rule:
`CandidateInference::candidate_conflicts` explicitly disclaims that interpretation.

The mathematical core is finite: Boolean and integer primitive shapes differ;
each program's generated constraints connects one positive primitive to a
different negative primitive. The source audit below establishes those
connections using existing constructors, rather than assuming a hypothetical
transition system. Actual parser acceptance, successful completion of the
experimental inference machinery for these exact bytes, and CLI/WASM observations
remain Luna's prescribed executable checks. No compiler, solver or runtime was
executed by this author. No inference soundness, principality, completeness,
termination, Call/effect theorem, Simple-sub A/B, source/native parent or production
gate is closed by this finite account.

The source provenance is external revision
`a58eefc31e22141574b6f20c6a5748151c6d79f1`, blob
`e6bec9fe44d673ccbf98af078ef4562c9267ef6c`, path
`web/playground/src/main.ts`, SHA-256
`baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90`.
The primary supplied the validated pinned-blob provenance; this author did not
read dirty external worktree bytes or perform Git operations. The two local
fixture files were read and their exact byte hashes checked:

| Example | Bytes | SHA-256 |
| --- | ---: | --- |
| `web/playground/examples/yulang2-type-mismatch.yu` | 77 | `9e5f99a3b96452f8775ab5657f489443430afcc4a5f85b048425e5b9400e3f2f` |
| `web/playground/examples/yulang2-parameter-provenance.yu` | 132 | `ed3339fe27331014efdc1a698c156a9b3bca04b8879ce9343b66cac0ec6e9a07` |

## Source owners and the two derivations

Write `B+`, `B−`, `I+`, and `I−` for the existing Bool/Int positive and negative
leaves, and `u <: v` for an admitted candidate value constraint. Row letters
below are explanatory names, not fabricated runtime IDs. In particular, an
original formal and its copied image must not be identified merely because they
serve the same source binder.

### Annotated Boolean initializer

The first template has a single binding, `my answer: int = true`. In
`module.rs::plain_binding_header`, local-source admission filters the
`PatternTypeAnnotation` from the binding target shape; it does not discard its
annotation. `module/local_source.rs::form` retains the root annotation via
`source_annotation::form` and forms the Boolean initializer. This account begins
at that retained HIR source; the exact syntax entry remains covered by the
primary's prescribed fixture verification, not an execution claim here.

`candidate_source.rs` allocates an expression component `v` and emits, for the
Boolean constructor, slots 0/1:

```text
B+ <: v       v <: B−
```

Its definition-root annotation branch schedules `Action::Annotation` with that
initializer endpoint and the root export component. The action's actual consumer
is `candidate_effect.rs::candidate_annotation`, through
`candidate_annotation_pair`. `candidate_signature_value` maps the retained Int
annotation to `I−` in negative polarity and `I+` in positive polarity. The pair
constructor checks the initializer against the annotation at slot 40 and exposes
the annotation at slot 41:

```text
v <: I−       I+ <: answer_root
```

The first edge, together with `B+ <: v`, produces the primitive pair `B+ <: I−`
by the candidate row replay described below. `incompatible_value_shapes` returns
`(Bool, Int)`. The separately exposed `I+` does not erase the initializer check
or authorize acceptance: the conflict is retained and tool preparation fails.
No use of `answer`, runtime definition selection, or evaluator action is needed.

### Argument provenance through an unannotated formal

The second template is exactly:

```yu
// The argument is an int, but the body uses value as a condition.
my choose(value) = if value:
    "yes"
else:
    "no"

choose 42
```

`module.rs::plain_binding_header` admits a sole `PatternCallTail` containing one
identifier pattern. `module/local_source.rs::form` copies the authentic
`HirParameterId` into `LocalSourceParameter`, binds its spelling lexically to
`LocalSourceResolution::Parameter(id)`, and constructs a Lambda around the body.
`Builder::conditional` retains an If with one condition/body pair and an else
body; it accepts `IndentedStatementBlock` children. The condition starts in the
enclosing lexical environment and therefore resolves to that parameter. The
top-level `choose` use is a module definition use, not a local shadow or formal
callee. Its Apply carries the literal `42` argument. This source contains no
braces, handler, recursion, annotation variable, or foreign continuation.

The candidate collector registers the Lambda's same parameter ID and recipe
position. A parameter Name's endpoint is
`CandidateEndpoint::Parameter(position)`, rather than its otherwise allocated
expression facade component (`candidate_source.rs`, endpoint construction).
`shadow_apply.rs::candidate_endpoint` maps this endpoint to
`parameter_live_base + position`. Call provenance records remain source owned;
the condition is a value use, not a synthesized function call on the formal.

For `If`, the actual constructor schedules `Action::ValueConstraint`, slot 50,
from the condition's endpoint to `BoolNegative`. Thus, for the original formal
row `p`:

```text
p <: B−
```

Both string branch values contribute to the If result and their effects join
the result effect. There is no constant condition selection. These result/effect
edges do not replace or remove the condition constraint. The string result is
unrelated to the required Int/Bool conflict.

The collector's Lambda recipe retains the parameter position and actual body
endpoint. `lib.rs::admit_lambda_fact` constructs the positive Function with the
negative parameter child and positive body result. For this unannotated
value formal, no annotation domain substitutes for that child. Its argument
therefore carries the `p <: B−` demand.

Definition scheduling and module-use routing preserve this demand through the
real copying operations. `candidate_scheme.rs::execute_candidate_graph_plan`
executes definition schedules before capture; `lib.rs::execute` subsequently
executes module expression schedules. A module Name action enters
`route_incoming`, which dispatches through `route_incoming_inner` to
`route_candidate_graph` when the candidate graph is present. Capture records
Function children and row bounds. `expand_row` includes exact negative upper
bounds of a local row; an older shared row retains its live bounds.

There are two relevant mapping cases, neither requiring raw identity equality.
When structural extrusion lowers the Function into a receiving row,
`candidate_extrusion.rs::candidate_extrude` visits its argument with opposite
polarity. Negative row copying traverses the row's upper bounds, keeps a primitive
`B−` unchanged, and installs it on the copied row through `Work::Bound`; rows at
an already adequate level are retained. For a later module use,
`prepare_candidate_fresh_use` gives each canonical source row one image for that
use, reconstructs Function children from that same image map, and
`freshen_candidate_graph_core` restores captured bounds using those images.
Primitive leaves retain their tags. Consequently the Function argument image
`p_use` still has `p_use <: B−`, whether it is fresh or shared. This is a finite
source association, not an assertion that unrelated copies, witnesses or
providers collapse to one row. Qualifying intrusion, if invoked by existing
machinery, is not replaced or bypassed here.

The literal constructor emits `I+ <: a` for the `42` component `a`.
`shadow_apply.rs::admit_candidate_fact` constructs the actual negative Function
demand with positive argument child `a`, and constrains the callee value against
it. `lib.rs` decomposes positive/negative Functions contravariantly in the
argument field, producing:

```text
I+ <: a       a <: p_use       p_use <: B−
```

Row replay yields `I+ <: B−`; `incompatible_value_shapes` returns `(Int, Bool)`.
This is argument-to-formal provenance. It is not a direct annotation conflict,
and no return value or evaluation of the If is needed to expose it.

## Actual candidate propagation and diagnostic consumer

`Action::Fact` uses normal fact admission; `Action::ValueConstraint` and annotation
checks use `candidate_scheme.rs::admit_candidate_value_link`. Each records the
real source occurrence/cause and enters `constrain_live_value`.

The candidate path must not be justified using the legacy body of
`lib.rs::apply_value_task`: with a candidate graph present, that function returns
`candidate_extrusion.rs::candidate_apply_value`. That owner selects a bound owner
and polarity, calls `candidate_insert_bound`, and calls `candidate_replay_bound`.
Insertion appends exact primitive bounds or direct row bounds and retains
physical evidence. Replay enumerates the opposite bounds and compares lower to
upper in the correct direction. It records diagnostic edges and drives the
existing contextual replay. Thus either admission order for the two bounds
produces the same needed primitive comparison once both are present. A row-row
link transmits the demand/lower evidence through successive such replays.

`lib.rs::dispatch_live_item` checks `incompatible_value_shapes` before ordinary
row handling. A non-Bottom positive primitive and a distinct negative primitive
produce a direct `IncompatibleValue` witness. Function decomposition records
argument diagnostic edges. The typed drain completes the diagnostic delta and
calls `replay_witness`, which reaches `report_incompatible` and
`report_solver_kind`; the latter adds a solver error. Duplicate suppression
does not turn a retained witness into successful typing. This identifies the
existing source-to-consumer path; it is not a new theorem about every contextual
replay, suspension, or diagnostic SCC.

## Preparation and publication boundary

`tools/inference-playground/src/lib.rs::prepare` rejects syntax diagnostics,
lowering failures and unsupported candidates separately. After candidate solve,
it checks `candidate_conflicts().is_empty()`. A nonempty list is formatted under
the candidate-type-conflict classification and returned as `Err`, rather than
returning `(hir, candidate)`. `infer_with_scoped_experiment` calls `prepare` before
export/render; `execute` calls it with `?` before `RuntimeProgram::from_hir`,
definition selection, source-schedule creation and machine execution. Independently,
`CandidateInference::export` refuses graph export whenever solved errors are
nonempty. Internal private graph capture can precede this check; this account
does not claim that no private graph data is ever constructed.

Accordingly the required compatibility observation is a candidate conflict from
both infer and execute preparation. A parser error, unsupported source, missing
definition, runtime failure, fuel exhaustion or accepted result is a falsifier,
even if its user-facing text mentions an error. Exact error text, order, span or
identity is not a theorem premise. These claims concern the existing experimental
tool's barrier, not production inference admission.

## Frozen dependencies, reuse and handoff

The following live bytes were independently SHA-256 checked by this author
against the contract pins. Baseline-tree and oracle-blob validation is the
primary's activation receipt, not a Git check claimed by this worker.

```text
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  crates/yu-hir/src/module.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
b404eacf20e30a59affb2ac49afab2d489d50ce25510bfd93b90352e4379ed3c  crates/yu-solver/tests/candidate_conditionals.rs
a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473  tools/inference-playground/src/lib.rs
```

`candidate_conditionals.rs` supplies existing regression intent for non-Bool
conditions and parameter/module routes; its tests were only read, not executed
or reused as proof of these two inputs. No historical conditional theorem or
R138 helper-cut fragment is imported. The finite native comparison and source
constructor correspondence above reduce R139's remaining work to independent
review and exact fixture observations; original general parent obligations and
their owners remain unchanged and OPEN. R135's brace decision remains pending.

Mutual TODO `R139-EXACT-OBSERVATION-1` belongs to Luna: freeze/review the candidate
implementation, run only the contract's serial CLI and Web checks, and require
the candidate-conflict classification plus absence of successful output. Inputs
are the two exact fixture hashes and reviewed source/output pins. The falsifier
is any earlier-stage rejection, acceptance, or entry into runtime construction.
No compiler patch is authorized if this observation fails; return its exact
stage and source owner to the primary. A green observation remains bounded
compatibility evidence and cannot promote a general theorem.
