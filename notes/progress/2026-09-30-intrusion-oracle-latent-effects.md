# Oracle latent-effect obligations for SCC intrusion

Date: 2026-09-30
Oracle: frozen Yulang2 `main` at `a58eefc3`
Status: source characterization; no equivalence or principality claim

## Ordinary Functions already carry effect identities

The Oracle's ordinary Function lowering allocates effect variables even when
the source contains no explicit effect-row or handler syntax:

- `crates/infer/src/lowering/expr/constraints.rs:7–24` creates an exact-pure
  effect constrained between `Bottom` and the empty row.
- `lowering/expr/lambda.rs:954–969` places an exact-pure evaluation effect on
  a lambda and derives its return effect from the body.
- `lowering/expr/tail.rs:1092–1109` represents that return effect as a
  variable endpoint.
- `lowering/expr/lambda.rs:1127–1168,1251–1264` allocates function, output,
  and body effects for a defined Function and gives an unannotated parameter
  the `never` negative effect.

Consequently, an effect-free polarized value graph is not a complete source
semantics for ordinary Function inference. Any source-level Oracle parity claim
for Function uses must model these effect endpoints and their boundary identity
behavior, even if the supported source syntax excludes explicit effect rows and
handlers.

## Forced identity and use behavior

The no-explicit-effect source fixture recorded in
`2026-09-30-intrusion-bounded-negative-counterexample.md` §§ “Forced effect
quantifier use-map characterization” and “Two annotated-parent source uses”
observes:

- local generalization initially selects no ordinary quantifier;
- recursive effect passthrough forces one effect identity into the scheme;
- two reads of that scheme freshen the forced identity independently;
- eleven unquantified effect identities remain shared across those uses.

The lowering path is in `lowering/expr/tail.rs:970–1011,1241–1419`; per-use
freshening and preservation of unlisted identities are in
`analysis/instantiate.rs:620–648,732–760,798–808`. The unannotated-parent
branch instead retains the live local value when forced quantifiers exist.
This is identity transport evidence only; the two reads have the same call
shape and do not establish effect denotation or handler hygiene.

The nominally guarded two-member Function SCC with three differently typed
incoming uses is a separate Oracle characterization in the same bounded
counterexample record. It shows ordered component publication, internal live
uses, distinct incoming value identities, and differing argument constraints.
Its production freshening maps are not keyed to individual uses, and its raw
reachability check does not prove transitive isolation. It does not establish
effect transport for a multi-member component.

## Implicit application stack behavior

The no-handler source subset still has a special interaction between argument
effects and call return effects. Frozen `tail.rs::make_app_with_origins`
allocates result-value, result-effect, and call-effect identities; it places
the argument computation's effect in the callee Function's argument-effect
slot and constrains callee evaluation and the call-return effect into the
application result effect (`lowering/expr/tail.rs:540–627`).

The call-return endpoint is stack-wrapped only under a narrower condition:
the callee expression is a local variable reference resolving to a live local
`Def::Arg`, that binding is marked `Unannotated`, and
`unannotated_call_frame_index` selects a frame whose scope is `Defined`
(`tail.rs:745–768,801–829`). Depending on active nested skeletons and
sub-syntax scopes, this can select the frame where the unannotated local was
introduced rather than the innermost frame. The selected frame keeps one
`SubtractId` per local `Def`; the first call allocates it, marks that call's
effect as `Empty`-subtractable, and registers the matching `pop` on that frame.
Each call, including later calls reusing the same ID, wraps its own call-effect
endpoint with `StackWeight::push(δ, Subtractability::Empty)`
(`tail.rs:769–796`). Thus the
empty-subtract fact is per first call-effect, while the push identity is
reused per selected frame/local binding.

The structural Function subtype step is not an independent four-coordinate
product rule when the lower Function's argument-effect slot is `Neg::Bot`.
In that case `constraints/machine/propagate.rs:212–270` constrains the upper
argument effect against the upper return effect after stripping leading
`Neg::Stack` wrappers and applies `both_from_right()` to the subtype weights;
otherwise it relates the upper argument effect contravariantly to the lower
argument effect with swapped weights. Return effects remain covariant with
the original weights. Unannotated lambda
parameters use `Neg::Bot` for `arg_eff`, while `wrap_lambda_param` puts the
body computation effect into the returned Function's `ret_eff`
(`lowering/expr/lambda.rs:954–969,1251–1264`).

This rules out treating latent effects as four independent value coordinates
in the current powerset Function encoding. A source-adequate extension needs a
meaning for cumulative call effects and the pure-argument passthrough law, as
well as a meaning for the implicitly generated push/pop weights and
`NonSubtract` transport. Those meanings cannot be inferred from identity
renaming alone. They remain distinct from handler matching and masking
hygiene: no handler is needed to trigger this application path. This source
audit records operational facts, not the successor's effect semantics or a
final-acceptance theorem.

### Source-level local-argument push/pop capture

A temporary instrumentation probe in a disposable worktree at the frozen
Oracle commit ran the existing source fixture `my h(x, f) = f x` with
`cargo test -p infer
unannotated_callback_return_effect_surfaces_without_empty_stack -- --nocapture`.
The test passed and retained scheme `'a -> ('a -> ['b] 'c) -> ['b] 'c`.
Instrumentation inside `unannotated_local_callee_return_effect` captured the
actual eligible branch: callee `DefId(2)`, selected defined frame 1, call
effect `TypeVar(18)`, and `SubtractId(0)`. That call effect had the declared
`Empty` subtract fact; its lower endpoint was a `Pos::Stack` with one
`push(0, Empty)` and its upper endpoint was the corresponding
`Neg::Stack(Var(18), push(0, Empty))`, while the selected frame contained the
matching `pop(0)`.

This directly confirms that an ordinary source callback call reaches the
special local `Def::Arg` path and installs the per-call push plus frame pop.
The selected frame's dynamic effect is thus source-reachable, not merely a
synthetic graph possibility. The test's scheme shows that the callback result
effect remains observable after generalization, but does not itself expose
the raw stack identity. This one-call trace proves neither the directed row
subtraction law nor preservation of effect behavior under intrusion, and it
does not characterize nested frames, repeated calls reusing one ID, or
handler hygiene. The instrumentation and worktree were removed; frozen Oracle
files were unchanged. Independent compiler-referee review confirms this
eligible path and the paired endpoints/pop. It also confirms the test's
finalized latent effect variable, while noting that the capture does not
exercise second-call ID reuse, an outer-frame selection through nested
skeletons, transport across generalization/instantiation, or the weighted
cancellation law.

### Repeated local calls reuse one frame identity

A follow-up disposable-worktree probe used source `my h(x, y, f) = (f x, f y)`.
The focused test passed. Instrumentation captured two calls to the same live
`Def::Arg` in the same defined frame 2: call effects `TypeVar(23)` and
`TypeVar(28)` both received `push(SubtractId(0), Empty)`. The frame contained
one matching `pop(SubtractId(0))`. The first call effect had the declared
`Empty` subtract fact for ID 0; the second had no subtract fact of its own.
The finalized scheme was
`'a -> 'b -> (('a | 'b) -> ['c] 'd & 'e) -> ['c] ('d, 'e)`.

This confirms the source-level allocation boundary: one subtract identity and
one frame pop are shared by calls to the same local argument within that
frame, while each call gets its own pushed call-effect endpoint and only the
first call-effect receives the declaration fact. This is an identity and
lifecycle observation, not proof that the push/pop pair cancels semantically,
that effect rows are preserved, or that this behavior is principal under
instantiation. The temporary instrumentation and worktree were removed; no
frozen Oracle file changed. Independent compiler-referee review confirms the
shared ID, distinct per-call endpoints, one frame pop, and first-call-only
declaration fact. It cautions that this does not prove one pop cancels both
pushes or that the second call's subtract fact is derivable; weighted closure
adequacy remains open.

## Specialization-level argument-effect interpretation candidate

The frozen specialization path gives an operational reason for retaining the
argument-effect slot. `apply_type` obtains runtime Function argument and
return shapes through `function_runtime_parts`
(`crates/specialize/src/solve/expr_solver.rs:286–289`,
`crates/specialize/src/solve/effect.rs:21–26`). In
`apply_known_function_arg` (`expr_solver.rs:363–390`), a runtime argument
shape whose extracted effect is pure is evaluated as a call value; its actual
evaluation effect is included in the call result. A `Thunk` with a non-pure
effect is passed as the argument and contributes a pure immediate argument
effect.
`call_result_shape` joins the callee evaluation effect, immediate argument
effect, and function return effect (`expr_solver.rs:456–505`).
`mono::Type::is_pure_effect` classifies `Never` and the empty effect row as
pure (`crates/mono/src/lib.rs:89–95`).

The observed specialization mode is selected by the runtime type shape, not
directly by denotational purity of inference `arg_eff`. Conversion
`runtime_function_type` encodes an effectful Function argument as
`Thunk{effect,value}` and resets the Function's `arg_effect` slot to pure
(`crates/specialize/src/types/mod.rs:399–425`). But `runtime_shape` only
unwraps syntactic `Never` and the empty effect row; an unresolved effect
variable represented as `OpenVar` becomes a `Thunk`, regardless of constraints
that may have existed before materialization. Conversely, a source variable
with only the recorded `Bot` lower and empty-row upper may materialize directly
to the empty row when its bounds remain available: `materialize_neu` omits a
`Pos::Bot` lower, materializes the remaining `Neg::Row([], Neg::Top)` upper,
and row materialization yields `EffectRow([])`
(`types/materialize.rs:163–175,193–213`). By contrast, an unquantified,
unsubstituted variable occurrence materializes as `OpenVar`
(`materialize.rs:266–280`). Both facts are directly established. Outside the
focused identity fixture below, source-generated paths into runtime Function
materialization have not been traced, so the report does not claim which
representation reaches application in general. Those paths must be tracked
before assigning a source meaning to either mode.

### Focused identity source capture

A temporary probe in a disposable worktree at frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` lowered `pub id x = x` and read its
finalized scheme predicate. The focused command was
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_oracle_runtime_effect_path_for_identity -- --nocapture`. It reported
one quantifier (`TypeVar(2)`), formatted scheme `'a -> 'a`, `arg_eff = Bot`,
and `ret_eff = Bot`. Thus this source's exact-pure body effect does not survive
as either a bounded effect variable or an `OpenVar` in the final scheme
predicate; runtime materialization receives `Never` at this return-effect
slot, which `runtime_shape` leaves plain. The probe did not isolate which
generalization/simplification pass turns the source effect into `Bot`, nor
trace the specialized application itself. This closes the source-to-scheme
question for one identity fixture only. The temporary test and worktree were
removed; no frozen Oracle file changed.

The temporary test body, appended to `crates/infer/src/lowering/tests/case_01.rs`
after its existing `use super::*;`, was:

```rust
#[test]
fn scratch_oracle_runtime_effect_path_for_identity() {
    let root = parse("pub id x = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let def = binding_def_and_order(&lower.modules, module, "id").0;
    let output = lower_binding_bodies(&root, lower);
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = match output.session.poly.defs.get(def) {
        Some(Def::Let { scheme: Some(scheme), .. }) => scheme,
        _ => panic!("expected finalized id scheme"),
    };
    let types = &output.session.poly.typ;
    eprintln!("quantifiers={:?}", scheme.quantifiers);
    eprintln!("scheme={} ", poly::dump::format_scheme(types, scheme));
    match types.pos(scheme.predicate) {
        Pos::Fun { arg_eff, ret_eff, .. } => {
            eprintln!("arg_eff={:?}", types.neg(*arg_eff));
            eprintln!("ret_eff={:?}", types.pos(*ret_eff));
            if let Pos::Var(var) = types.pos(*ret_eff) {
                eprintln!("ret_eff_var={var:?}");
                eprintln!("ret_eff_bounds={:?}",
                    output.session.infer.constraints().bounds().of(*var));
                eprintln!("ret_eff_is_quantified={}", scheme.quantifiers.contains(var));
            }
        }
        _ => panic!("expected Function predicate"),
    }
}
```

The captured output was:

```text
quantifiers=[TypeVar(2)]
scheme='a -> 'a
arg_eff=Bot
ret_eff=Bot
test lowering::tests::case_01::scratch_oracle_runtime_effect_path_for_identity ... ok

test result: ok. 1 passed; 0 failed; 1393 filtered out
```

### Candidate cause of this fixture's effect elimination

A subsequent static trace identifies polar simplification as the first pass
that can account for this `id` result. `lower_name` creates the exact-pure
effect variable; lambda lowering places it in positive `Fun.ret_eff`;
compaction preserves a self occurrence even when its selected lower is only
`Bot`; generalization then runs alias expansion followed by simplification.
Alias expansion adds occurrences, while simplification eliminates eligible
variables seen at only one polarity before quantifier selection. An empty
positive effect slot finalizes to `Pos::Bot`, consistent with the captured
scheme.

This is a conditional causal explanation, not an observed intermediate
snapshot: it depends on this effect variable being eligible at the
generalization boundary and having no hidden negative occurrence, selected
non-`Bot` lower, or other role/recursive use. It establishes neither that
`Bot ≤ e ≤ Row([], Top)` denotes only the empty effect nor that polarity-only
elimination preserves source constraints. The successor may retain this
identity and its constraints; Oracle's simplification is characterization
evidence only.

### Exact-pure source effects in small finalized schemes

A focused test in a disposable worktree at frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` lowered three sources:

```yu
my make = \x -> 1
```

```yu
my apply(f) = f ()
my use = apply (\x -> 1)
```

```yu
my apply(f) = f ()
my make = \x -> 1
my use = apply make
```

All three lowered without errors. The finalized schemes were `make: any ->
int`, `apply: (() -> ['a] 'b) -> ['a] 'b`, and `use: int`. For both `make`
schemes, the outer Function had no quantifiers and finalized
`arg_eff = Bot`, `ret_eff = Bot`. The callback effect variables in `apply`
belong to its independently inferred argument/result relation; this probe does
not identify either as the bounded exact-pure variable introduced by the
lambda literal.

These cases do not show a bounded exact-pure variable at the finalized outer
Function effect endpoints; those endpoints are `Bot`. They do not establish
whether the source variable survives elsewhere in the complete predicate.
Positive scheme collection starts from a self-variable occurrence and reads
selected lower records; it does not itself erase that identity, and the upper
empty-row bound is not directly included by that projection. Later
polar simplification may erase the variable if it is eligible. No intermediate
graph or full raw predicate traversal was captured, so these probes do not
prove the elimination point or the denotation of
`Bot ≤ e ≤ Row([], Top)`. Under the user's successor direction, Oracle's
polarity-based simplification is not a required behavior: preserve the source
interval until a semantics proof justifies replacing it with a pure effect.
The focused probe and this static source-path review were independently
checked; neither proves the runtime behavior or principality of the successor.

### Dual-polarity source occurrence in a catch continuation

A focused test in a disposable worktree at frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` lowered:

```yu
act tick:
  our ping: () -> never

my f = catch 1:
  ping(), k -> k
  v -> \() -> v
```

The test passed with no lowering errors. The scrutinee's fresh exact-pure
effect identity was `TypeVar(3)` in this run. Raw lowering bounds for local
continuation `k` put that same identity in both Function return-effect
polarities: lower `Pos::Var(TypeVar(3))`, upper `Neg::Var(TypeVar(3))`. Its
upper bounds included `Row([], Top)` and a handled-`ping` row. The active bound
view did not list a `Bot` lower, but that does not show the original
`Bot ≤ e` source constraint is absent; the bound store can omit the trivial
lower. The finalized root scheme was `() -> int`, with no quantifiers and
`ret_eff = Pos::Bot`.

This proves dual polarity in the source-generated continuation constraints,
not in the selected compact root for `f`. It also does not show that the same
identity or both bounds survive finalization. Independent compiler-referee
review confirmed this distinction and cautioned that local `k`'s two-sided
shape cannot establish the root projection or whether erasure changes final
acceptance. A variation returning `[k]` through `list` also lowered, and its
final scheme retained a more complex handled-effect interval, but did not
identify the original `TypeVar(3)` in that interval. Neither fixture justifies
polarity-only erasure in the successor: keep meaningful source constraints
until a preservation argument shows which ones can be solved or removed.

The focused command was
`CARGO_TARGET_DIR=/tmp/yulang-pure-dual-target cargo test -p infer
scratch_pure_dual_catch_continuation -- --nocapture`. The disposable test and
worktree were removed; frozen Oracle was unchanged. This only tested inference
lowering/finalization, not full compilation or execution.

A second disposable test added the root expression `f()` and sent the same
source through Oracle's production `specialize` entrypoint. `lower_source`
reported no body-lowering errors; specialization succeeded and produced the
root call `(m0 ())` with instance `m0 = d2 : unit -> int`. The raw instance
signature had `arg_effect = EffectRow([])`, `ret_effect = EffectRow([])`, and
return type `int`. An independent compiler-referee review confirms this is
full source-lowering-to-mono acceptance for this fixture, stronger than the
inference-only probe. It still does not reveal the exact final fate of
`TypeVar(3)` inside the selected root, prove its source bounds redundant, or
show runtime/backend acceptance or successor adequacy. The disposable test
and worktree were removed. The focused commands were:

```sh
CARGO_TARGET_DIR=/tmp/yulang-pure-dual-target cargo test -p infer scratch_pure_dual_catch_continuation -- --nocapture
CARGO_TARGET_DIR=/tmp/yulang-catch-finalaccept-target cargo test -p specialize scratch_catch_continuation_exact_pure_effect_reaches_mono -- --nocapture
```

A separate attempt to use the `wasm` runtime test path was stopped before the
test ran: its build script was compiling both embedded standard libraries and
reached about 1 GiB RSS after 2m46s. That run supplies no runtime evidence.
The attempted command was
`CARGO_TARGET_DIR=/tmp/yulang-catch-finalaccept-target cargo test -p wasm scratch_catch_continuation_exact_pure_effect_executes -- --nocapture`.
A CLI `check` attempt on the same `/tmp` source was also stopped before a
result after it remained CPU-active for over a minute at roughly 0.7 GiB RSS;
it supplies no independent CLI acceptance result. The attempted command was
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo run -p yulang --bin yulang -- check /tmp/yulang-catch-dual.yu`.

### Exact selected-root observation boundary

A read-only source trace located where to settle the remaining correspondence
question. During member generalization,
`analysis/session/generalize.rs::compact_root_for_generalize` calls
`compact_type_var_recording_merge_constraints_for_scheme`, which creates a
scoped legacy projection query in `compact/surface.rs` and invokes
`CompactCollector::compact_root_with_merge_constraints_for_scheme`. The
collector starts at the member root with positive polarity; when it reaches a
Function return-effect slot it recursively collects that slot, while
`compact_var_side` selects positive lower records and negative upper records.
The query exposes `scheme_projectable_lowers_in_scope` and
`projection_upper_records_in_scope`. A decisive fixture capture must record,
in the same query, those selected records for the source effect identity and
the returned `CompactRoot` before
`simplify_compact_root_with_roles_and_non_generic` runs. The collector does
not persist a selected-record snapshot after quantification.

This narrows the unresolved claim: raw post-lowering bounds and local `k`'s
dual Function-bound incidence do not show that `f`'s selected compact view
traverses or retains those bounds. Simplification can still omit a
one-polarity variable. This is an observation boundary, not a justification
for erasure: per the user's rule, the successor retains meaningful source
constraints until a denotation and preservation argument justifies solving
or removing them. No code or frozen Oracle file was changed for this mapping,
and no additional check was run.

### Selected-view probe for the catch fixture

A temporary instrumented test at frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` captured the actual `f` root
projection in the same scoped query. The run-local identities were `f =
DefId(2)`, root `TypeVar(1)`, and source effect `TypeVar(3)`. The positive
collector visited `TypeVar(3)` in `Fun.ret_eff`; its actual
`scheme_projectable_lowers_in_scope` result was empty. Two upper rows were
available in that same query (`BoundRecordId(1)` and `BoundRecordId(25)`), but
the positive collector path asks for projectable lowers only. The returned
pre-simplification `CompactRoot` retained `TypeVar(3)` as a positive
self-occurrence alongside `TypeVar(11)`. The post-alias/simplification root
had no `ret_eff` variables.

This establishes a fixture-level polarity-selected projection gap: the two
available upper rows did not enter `f`'s compact root at that positive visit.
A follow-up trace instrumented the actual simplifier. Pinned-interval collapse
left the root unchanged; the first fixed-point iteration of
`eliminate_polar_variables_with_roles_and_non_generic` returned
`TypeVar(3) -> None`, immediately removing it. The following co-occurrence pass
made no substitution. Independent compiler-referee review confirms this
attributes the disappearance from this prepared root to polar elimination,
with eligibility and one-polarity occurrence measured after alias expansion.
It does not establish one-polarity occurrence in the complete source graph,
nor that the skipped empty/handled-effect upper rows are semantically
meaningful for this root. They may be redundant for this pure fixture or may
have influenced another selected constraint. Neither soundness nor
principality failure follows from this fixture, and the already recorded
`f()` mono acceptance still passes. The successor requirement remains to
retain meaningful source constraints and justify any solving/removal by its
own denotation and preservation proof; matching Oracle's selected view is not
a goal. The focused commands were
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_capture_selected_catch_effect_view -- --nocapture` and
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_capture_catch_simplification_trace -- --nocapture`; both passed. All
temporary instrumentation and tests were restored from the disposable Oracle
worktree, which is clean at the frozen commit.

### Separate residual-effect final-acceptance witness

A second complete source fixture exercises a different effect obligation:

```yu
act signal:
  our ping: () -> never
act io:
  our read: () -> int

my judge(x: [_] _) = catch x:
  signal::ping(), _ -> true
  _ -> false
judge(io::read())
```

The frozen Oracle's `specialize` accepted this through mono construction. The
emitted instance signature was
`Thunk{[signal, io], int} -> Thunk{[io], bool}`; the body carried a
`[signal]` marker, made a thunk for the argument under `[signal, io]`, and
forced it with `[io]` remaining. The root forced the result under `[io]`.
This is a concrete source-to-mono witness that specialization preserves an
unhandled residual effect while compiling a handler that accounts for
`signal`. It was inspected as generated IR only; no program was executed.
This fixture does not identify the catch-1 `TypeVar(3)` upper rows or show
that they are meaningful. It supplies a nearby acceptance fixture for future
source-constraint and effect-transport proofs, not evidence for the intrusion
successor.

The temporary test and changes were restored from the disposable frozen
Oracle worktree. Focused command:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p specialize
scratch_specialize_residual_handler_effect_use -- --nocapture`.

### Source rule and complete/incomplete handler constraints

The source path behind this residual-effect witness is now mapped. An act
operation's declared family is inserted into its return effect, so the fixture
has distinct `[signal]` and `[io]` effects; application lowering propagates
the operation return effect into the call computation effect. The catch arm
for `signal::ping` adds the `[signal]` row. Its unguarded wildcard payload
covers the sole operation in that act, so the handler is complete. The
complete-handler branch constrains the scrutinee effect to
`[signal; result_effect]` without directly copying the scrutinee effect into
the result. Row residual reduction removes `signal` and routes the unrelated
`io` family to the tail.

Two existing focused inference tests cover this branch distinction. A
complete handler over `run = 1` has no result-effect lower source with an
`out` row upper; an incomplete handler for one operation in a two-operation
`choose` act retains a result-effect lower source with a `choose` row upper.
Both tests passed. They inspect the inference constraint graph only, not
selected compact roots or generalized schemes. A nearby committed test's
expected scheme `any [ping; 'a] -> ['a] bool` likewise shows a retained
residual binder, but is not the exact `judge` fixture.

The compiler-referee review of the mono witness confirms its scope: the
generated instance accepts `[signal, io]` input and returns `[io]`, with a
`[signal]` marker and an `[io]` force in the body. This is compilation and IR
evidence, not execution or a general subtraction theorem. No raw inference
TypeVar IDs, selected `judge` root, or finalized `judge` scheme have yet been
captured, so the path from these source constraints through generalization
remains open. This witness is distinct from the `catch 1` `TypeVar(3)` case;
it does not prove those omitted upper rows meaningful. The focused inference
commands were:

```sh
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer catch_complete_effect_handler_flows_rest_effect_to_result -- --nocapture
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer catch_incomplete_effect_handler_flows_scrutinee_effect_to_result -- --nocapture
```

The useful candidate is thus a two-mode *runtime application* judgment:
shapes with pure extracted effects are evaluated strictly and their actual
effect is charged to the call result; shapes with non-pure extracted effects
are passed as deferred computations and contribute no immediate argument
effect. This motivates why Function application is not a four-coordinate
product, but it does not yet explain how
the inference argument-effect slot determines that runtime shape or prove
that it corresponds to the inference rule's `Neg::Bot` passthrough branch.

There are two distinctions to resolve. First, the inference branch tests
whether the lower argument-effect endpoint is syntactically `Neg::Bot`
(`propagate.rs:234`), while an exact-pure evaluation effect is represented by
a variable with bounds `Bot ≤ e ≤ EmptyRow` (`constraints.rs:7–24`). Second,
specialization chooses strict versus deferred application by testing whether
the effect extracted from the runtime argument shape is syntactically pure.
Whether an exact-pure inference variable reaches this check as `OpenVar` or as
the empty row depends on materialization and remains untraced. A
successor need not preserve either Oracle phase rule, but its independent
source judgment must define the inference-to-runtime shape mapping and prove
the final behavior. Effect denotations alone cannot explain the distinction
if these representations collapse to one pure element.

The runtime path does not define the denotation of inference `StackWeight`,
`SubtractId`, weighted row residuals, or `NonSubtract`. A `SubtractId` is a
scoped administrative identity: `StackWeight` normalizes ordered push/pop
entries noncommutatively (`poly/src/types.rs:298–400`), while lowering reuses
one identity per selected frame/local binding and records subtractability on
the first call effect. It cannot be erased as an effect-family label without
a contextual preservation proof. In particular, it is not yet proved that
the local-call push/pop pair is a semantics-preserving encoding of either
runtime application shape. A discriminating source fixture must compare a
callee whose finalized argument becomes a plain runtime value shape with one
whose argument becomes `Thunk{effect,value}`, each applied to an effectful
expression, and observe final acceptance, argument evaluation, and resulting
computation effect. It must separately inspect an exact-pure inference
variable's runtime conversion. A nested call through an unannotated local
`Def::Arg` is additionally needed to exercise the selected-frame push/pop
path. These fixtures and their independent declarative typing derivations
remain unestablished.

### Candidate mode-indexed application obligation

The smallest adequate source judgment cannot choose a mode from the denotation
of an effect variable alone. For an elaborated runtime argument shape `S`,
define `split(S) = (A, ε)` as follows: `split(Thunk(ε,A)) = (A,ε)` and
`split(A) = (A, ∅)`. Oracle's source path then has two application cases:

```text
Strict:
  pure_mono(ε) = true
  evaluate argument to value A, obtaining its actual computation effect εeval
  argument contribution to result effect = εeval
  pass A to the callee

Deferred:
  pure_mono(ε) = false
  pass Thunk(ε,A) to the callee
  argument contribution to result effect = ∅
  retain ε as the thunk's latent effect, to be accounted for if forced

Both:
  total application result effect = εret ⊔ εcallee ⊔ argument contribution
```

Here `pure_mono(ε)` is the runtime predicate: it holds for `Never` and
`EffectRow([])`. The split returns the effect stored by any thunk, including a
syntactically pure one; mode selection applies the runtime predicate to that
extracted effect rather than testing for an empty-row constructor alone.

This is a candidate *specialization judgment*, not a declarative typing rule
or a successor decision. It reflects `apply_known_function_arg`'s branch on
the effect extracted from the runtime computation shape, and its result joins
the callee effect with the strict argument's actual effect. The non-pure case
passes `runtime_shape(ε,A)` and uses a pure immediate argument effect. Boundary
adaptation and any later force must be included before claiming whole-program
effect preservation. The extracted return effect `εret` is also joined by
`call_result_shape`; it is included above so the argument-mode rule is not
mistaken for the whole result-effect rule.

The successor proof therefore needs a relation
`Shape(Γ,C,A,ε,m,S)` connecting a source computation and its inference graph to
its elaborated runtime shape and mode. For each fixed outer assignment it
must show that inference lowering plus materialization selects a legal mode,
that the selected runtime adaptation preserves evaluation and effect behavior,
and that constraints retained on shared effect identities remain visible
through that transport. It must establish principality for the overall typing
and root relation, and coherence if more than one elaborated shape can realize
the same source computation. The mode itself is deterministic for a fixed
materialized shape; there is no separate ordering on `Strict` versus
`Deferred`. No such relation is
proved here. In particular, a candidate `m = (⟦ε⟧ = ∅)` is not justified:
Oracle branches on the materialized runtime shape, while bounded pure
views and open effect variables can have different materializations.

The minimum discriminating characterization remains: compare an effectful
argument passed to a function whose parameter expects a plain value with one
whose parameter expects an effectful thunk; inspect finalized argument
effects, generated `MakeThunk`/`ForceThunk`, and final behavior. Separately
trace a surviving exact-pure effect variable through materialization and an
eligible nested unannotated local call through its selected frame's
`SubtractId` push/pop. Existing thunk-specialization coverage establishes
only shape preservation, not the source typing derivation or general bridge.

### Temporary plain-value versus thunk-parameter probe

A temporary focused test in a disposable worktree at frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` compared:

```yu
act out:
  our read: unit -> int

my strict(x: int) = 1
strict(out::read(()))
```

with the same source using `my defer(x: [_] int) = 1` and
`defer(out::read(()))`. The command was
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p specialize
scratch_oracle_argument_mode_pair -- --nocapture`; it passed both
specializations. The strict instance had signature `int -> int` and emitted a
root `ForceThunk` for the `[out]` read computation. The deferred instance had
signature `thunk[any, int] -> int` and emitted a root `MakeThunk` whose body
contains the `[out]` `ForceThunk`. Since both functions ignore their argument,
this is a concrete specialization distinction: the plain-value boundary
forces the effectful argument, while the thunk-parameter boundary leaves it
suspended in a thunk.

This inspects generated mono structure; it does not execute the program or
prove its operational semantics. It also does not inspect finalized inference
effect endpoints, a surviving exact-pure variable, the application result
effect in a non-inlined call, or an unannotated local `Def::Arg` push/pop.
The temporary test and worktree were removed, and the frozen Oracle checkout
was not changed. Independent compiler-referee review confirms the narrow
shape/adaptation distinction and notes that runtime `MakeThunk` stores its
body for later evaluation, while `ForceThunk` evaluates it. The run itself did
not execute either program. The `thunk[any, int]` signature is the callee's
runtime parameter shape after boundary adaptation; it does not show that the
inference argument-effect slot denoted `Any` (the generated `MakeThunk` has
source effect `[out]` and target effect `any`). The review found no defect in
this fixture and does not establish exact effect accounting or the general
inference-to-runtime theorem.

An independent compiler-referee review of this candidate section found and
closed three local issues: the total result effect must include `εret`; the
runtime purity predicate accepts both `Never` and `EffectRow([])` after
splitting a thunk/plain shape; and mode determinism is not a separate
principality order. The repaired statement is still only a specialization
characterization. The reviewer did not certify the source-to-shape relation,
the effect carrier, weighted transport, or the overall soundness/principality
claim.

### Finalized inference-endpoint follow-up

A second temporary probe of the same source pair printed every finalized
Function scheme's raw argument and return effect nodes before specialization.
The operation scheme was `() -> [out] int`, with
`arg_eff = Row([], NegId(1))` and `ret_eff = Row([PosId(0)])`. The plain
parameter function had `arg_eff = Bot`, `ret_eff = Bot`; the thunk-annotated
function had `arg_eff = Top`, `ret_eff = Bot`, although both ordinary scheme
format strings rendered as `int -> int`. Specialization then materialized
those two shapes as `int -> int` and `thunk[any, int] -> int` respectively.

For this fixture, this supplies a concrete inference-to-runtime observation:
the finalized positive Function predicate for the deferred fixture has
syntactic `Neg::Top` in `arg_eff`; this path materializes that to `Any`, then
`runtime_shape` makes `Thunk(any, int)`. The strict fixture's `Neg::Bot`
materializes to `Never` and remains a plain `int` argument. The operation's
`[out]` effect is carried by its result computation inside the thunk; the
target `any` on `MakeThunk` comes from boundary adaptation, not from the
operation's effect. Both text schemes render as `int -> int`, which matches
the user's decision not to require inference-stage scheme-format compatibility.

Independent compiler-referee review confirms these links for this exact pair:
`Neg::Bot`/`Neg::Top` in the finalized positive Function predicate,
materialization to `Never`/`Any`, and runtime conversion to plain/thunk
arguments. This does not show that source lowering originally allocated
`Top`, that `Top` denotes the concrete `[out]` effect, or that all deferred
arguments use `Top`.

This is still one pair of finalized schemes, not a general shape relation or
proof. It says nothing about a surviving bounded exact-pure effect variable,
non-inlined result-effect accumulation, independent use substitutions, or
weighted local-call transport. The temporary test and worktree were removed;
the frozen Oracle was unchanged. Independent review of this endpoint mapping
remains pending.

The runtime-shape rule and explicit inference-to-runtime bridge are therefore
source-grounded candidates for ordinary application, not a selected carrier
or design decisions. Before they can support implementation, a successor
must give independent meanings to latent effect rows and weighted transport,
prove the Function compatibility rule sound and principal for that judgment,
and show source lowering adequate for each fixed outer assignment. It may
discard Oracle's syntactic `Neg::Bot` branch or its runtime extracted-effect
purity test only after the declarative judgment proves corresponding final
behavior.

## Directed-weight evidence and a conditional simplification

The frozen Oracle effect-subtraction specification
(`spec/2026-05-31-effect-variable-subtractable.md`, §§ “Directed weight”,
“Weight composition”, “Row upper bound”, and “Protect”) defines noncommutative
per-identity weights. A push carries a `take(F)` family budget; pops cancel
only takes that precede them. For a weighted upper row with head `K`, only
active left pushes can consume families, with `J = K ∩ Common(L)`. Right
pops do not widen the head. `take(Empty)` is a protective boundary: its
`Common(L)` is empty, so it cannot consume any row head. Terminal concrete
types do not observe weights, but rows and nested Functions can.

This gives a conditional reduction target for a handler-free, no-effect-family
fragment: if every reachable row split has an empty head `K`, then
`J = ∅` regardless of active push families, and no residual is produced by
that split. For arbitrary `K`, a separate sufficient premise is that every
relevant `L` has at least one active `take(Empty)`, which makes
`Common(L) = Empty`; alternatively prove `Common(L) = Empty` directly.
Having only empty takes is insufficient when there are no active pushes,
because the specification defines `Common(L) = All` in that case. These
premises could support a zero-consumption lemma for the fragment; neither is
established for source-generated graphs yet. `StackWeight` IDs
must still be transported as scoped identities until the weighted-closure
simulation proves when they may be erased.

The premise that `fresh_exact_pure_effect` really denotes only the empty
effect also remains open in an independent carrier. Its source constraint is
`Bottom ≤ e ≤ Neg::Row([], Neg::Top)`; the helper name does not define the
meaning of the polarized empty row or its tail. A candidate semantics must
define that interval, inspect all generated weighted row splits, and prove
the zero-consumption premise before using this reduction to simplify
ordinary Function effects. This is separate from, and does not discharge, the
inference-to-runtime argument-shape bridge above.

### Nested active skeleton selects the enclosing call frame

A disposable test was added to a separate worktree at the frozen Oracle
commit. The source was:

```yu
my outer(l: int, sink): int =
  my inner(x) =
    sink x
    inner l
    x
  my first = inner l
  my second = inner l
  second
```

The focused `infer` test passed and temporary instrumentation observed the
unannotated local `Def::Arg` call to `sink`: the call site's introduced frame
was 1, the currently innermost defined frame was 2, and
`unannotated_call_frame_index` selected frame 1 with two active defined
skeletons. Follow-up instrumentation confirmed the last frame was `Defined`,
`direct_defined_call = true`, and `crosses_inner_active_skeleton = true`, so
the active-skeleton crossing branch selected the introduced outer frame rather
than the sub-syntax fallback. That frame had one `pop(δ0)`, while the call
carried a matching `push(δ0, Empty)`. This is a concrete nested-skeleton
outer-frame selection path, unlike a typed `sink` parameter, whose annotation
bypasses this branch. The observed final outer scheme was
`int -> (int -> ['a] any) -> ['a] int`.

This confirms source reachability and branch attribution for this fixture; it
does not prove that the pop cancels all pushes, that the generated weighted
closure is sound/principal, or that the result is adequate for arbitrary
source programs. An independent compiler-referee review caught and closed the
branch-attribution gap by requiring direct-call and active-skeleton predicate
evidence; the follow-up trace includes those facts. The temporary test,
instrumentation, and worktree are disposable characterization only; frozen
Oracle files were not changed.

## Consequence for the full redesign goal

The effect-free Function graph in the abstract-semantics draft can serve as a
component lemma only. It cannot be the end-to-end source envelope or the
acceptance boundary for the user's Oracle-capability objective. The successor
semantics must eventually account for latent effect bounds, forced
generalization, use-site freshening, preserved shared identities, and the
sequential root/publication lifecycle. Handler matching, masks, weights, and
runtime freshness remain separate obligations until the supported source
envelope says they are admitted.

No Oracle code was changed. The focused test ran only in a disposable worktree;
the frozen source paths and probe records above are the evidence.

### Selected `judge` root and residual binder

A disposable focused `infer` test instrumented the accepted source:

```yu
act signal:
  our ping: () -> never
act io:
  our read: () -> int

my judge(x: [_] _) = catch x:
  signal::ping(), _ -> true
  _ -> false
judge(io::read())
```

In this run, `judge` was `DefId(4)` with root `TypeVar(2)`. Before alias
simplification, its compact root placed `TypeVar(11)` in both the argument
effect row tail and return effect. The argument tail also included `signal`;
the pre-simplification return effect had additional identities, including
`TypeVar(23)` carrying `SubtractId(0)` / `AllExcept(["signal"])` weight.
After alias simplification the root was
`Fun(arg_eff=[signal; TypeVar(11)], ret_eff=TypeVar(11), ret=bool)`, and the
formatted scheme was `any [signal; 'a] -> ['a] bool` with sole quantifier
`TypeVar(11)`.

The selected positive occurrence of `TypeVar(11)` had four admitted lower
records: 39 (unweighted `PosId(29)`), 43 (unweighted `PosId(22)`), 45
(unweighted `PosId(25)`), and 47 (`PosId(28)` weighted by
`AllExcept(["signal"])`). Their projection evidence was qualified standalone
or replay-conjunction evidence. This shows that the residual binder in this
saved selected view is not merely an unconstrained fresh variable, and that
its argument-effect and return-effect positions share one binder in the
finalized scheme.

This observation does not identify any record or `TypeVar(11)` with `io`:
`io` enters at the use site, while the scheme binder is polymorphic. The
instrumented positive occurrence is one traversal, not proof of global
single-polarity use; the binder appears under Function argument-effect
variance too. Nor does the trace prove that the weighted record's meaning
survives alias simplification, establish freshening/adequacy for every use, or
prove principality. In conjunction with the prior `judge(io::read())`
specialization witness, it characterizes one accepted source-to-mono residual
effect case, without runtime execution.

The focused test and instrumentation were restored from the disposable
Oracle worktree after capture. Independent compiler-referee review accepted
the same-TypeVar linkage and selected-view claim with the limits above. The
successor requirement is now explicit: retain meaningful source constraints;
polarity-only `q` erasure is not required, and any later erasure needs a
preservation proof. Oracle inference-stage scheme formatting and its
acceptance phase need not match the successor; compatibility is measured by
final well-typed program acceptance, subject to soundness and principality.

### Bound provenance for the selected residual view

A second disposable test queried the four admitted lower records while the
`judge` inference session was still alive. Their endpoints and raw derivations
were:

| Record | Owner / endpoint | Derivation | Explanation source leaves |
| --- | --- | --- | --- |
| 39 | `11 <- 14` | `Constraint(33)` | none |
| 43 | `11 <- 19` | `Constraint(35)` | none |
| 45 | `11 <- 22` | `Constraint(36)` | none |
| 47 | `11 <- 23`, weighted `AllExcept(signal)` | `Constraint(37)` | annotation origins 2 and 3, boundaries 0 and 1 |

The source-free explanations report `UnknownInternal` derivation roots; the
weighted record's explanation is complete and reaches two `Annotation`
source leaves. In the same run, `TypeVar(14)` has lower endpoints 19, 22, and
23, and upper endpoints 11 and 9. This exposes the selected residual's local
constraint graph and confirms that the weighted path is attached to that
graph. The provenance API does not resolve annotation spans, and those leaves
do not identify the `io` call or prove the semantic effect contribution of
any one path. In particular, the selected record IDs are session-local
insertion indices, not durable source identities; reproducing them requires
the same session and insertion order.

The trace was run with a focused crate-local test in the disposable Oracle
checkout and then restored. It narrows the next source-origin question to the
two annotation boundaries and the internal/replay derivations, while leaving
the candidate semantics, effect preservation, and principality obligations
open.

### Resolve the two annotation boundaries

The exact boundary allocation path for the `judge` fixture is now mapped:

- `OriginId(2)` / `SourceBoundaryId(0)` is the whole parameter annotation
  `x: [_] _`. `connect_lambda_pattern_annotation` creates an
  `AnnConstraintLowerer::with_vars_and_closed_effect_rows` for it.
- `OriginId(3)` / `SourceBoundaryId(1)` is a declared subtract fact created
  while that same lowerer processes the wildcard effect row `[_]`. The path is
  parameter-computation connection, effect-row stack construction, stack-fact
  registration, then `InferArena::declared_subtract_fact`.

These are two provenance leaves from one source annotation, not separate
annotations and not the `signal.ping` / `io.read` operation signatures. Those
operation signatures use `SignatureLowerer`; the plain signatures in this
fixture do not allocate these `Annotation` boundaries. A disposable trace
propagating caller locations through the allocators logged the first boundary
at the annotation-lowerer constructor and the second at its stack-fact
registration. Independent source audit confirmed the lowering path. Since the
annotation source-boundary table does not retain annotation spans, this
mapping rests on the exact fixture and unique allocation/call order, not a
stored source location.

This narrows the provenance claim for weighted record 47: its source leaves
come from the annotated input effect contract and its generated subtract fact.
It still does not show that `io` is the denotation of the quantified `'a`,
that the weighted relation survives simplification in the successor, or that
the source-to-mono witness generalizes. Both the allocator instrumentation
and focused test were restored from the disposable checkout.

### Same-family complete/incomplete handler roots

A focused disposable test compared two definitions over the same two-operation
family `choose`:

```yu
act choose:
  our branch: () -> int
  our reject: () -> never

my complete(x: [_] _) = catch x:
  choose::branch(), _ -> true
  choose::reject(), _ -> false
  _ -> false

my incomplete(x: [_] _) = catch x:
  choose::branch(), _ -> true
  _ -> false
```

Both definitions lower without errors and both formatted schemes are
`any [choose; 'a] -> ['a] bool`. A temporary trace at
`compact_root_for_generalize`, before alias/simplification, captures different
`ret_eff` evidence: `complete` has a secondary occurrence weighted by
`push(δ, AllExcept(choose))`; `incomplete` has a secondary occurrence weighted
by `push(δ', All)`. Their TypeVar and SubtractId numbers differ because these
are separate definitions and carry no cross-definition identity claim.

This is the first same-family selected-view characterization that shows a
coverage-correlated weight distinction hidden by formatted schemes. It does
not isolate coverage as the only cause (the complete function has another arm
and body), prove that either weight survives finalization, interpret weights
as concrete effect rows, or show that `choose` is removed/retained at a use
site. It also does not establish final monomorphic acceptance, runtime
behavior, or principality. The compiler-referee review accepts the narrow
pre-simplification distinction and these limits. The focused test and trace
instrumentation were restored from the disposable Oracle checkout.

### Finalization and mono use of the same-family pair

The same source pair was extended with uses of both definitions on
`choose::reject()`:

```yu
my complete_use = complete(choose::reject())
my incomplete_use = incomplete(choose::reject())
```

The production Oracle CLI accepted the exact file through both
`--no-prelude --no-cache check` and `--no-prelude --no-cache dump … --mono`.
The mono output contains roots for both uses. Both function instances have
`thunk[[choose], unit] -> bool`; the complete body retains branch and reject
arms, while the incomplete body retains only branch. Both generated bodies
include `catch marker[choose](force-thunk[… ! [choose]])`.

The raw poly dump gives alpha-equivalent finalized type predicates for the
two functions: one effect quantifier, `arg_eff = Row([choose], tail: 'a)`,
`ret_eff = 'a`, and no stack quantifiers. Thus the observed pre-simplification
`AllExcept(choose)` versus `All` weight difference is absent from these
finalized type schemes. This does not establish that all selected-view data is
erased: provenance sidecars and other publication fields were not compared.
Nor does it prove that the earlier weight was semantically redundant or that
the two effect computations execute with different outcomes. The direct mono
root's exact adaptation was not isolated in that probe, so it remained unclear
whether the operation thunk was forced before or inside the handler. A follow-up
uses a named thunk binding to remove that ambiguity; see the next section.

The exact CLI commands were:

```text
yulang --no-prelude --no-cache check /tmp/yulang-handler-coverage-probe.yu
yulang --no-prelude --no-cache dump /tmp/yulang-handler-coverage-probe.yu --mono
```

Both commands completed successfully with the prebuilt binary from the
disposable Oracle checkout. This proves final mono acceptance for those exact
source programs only. The disposable source and all instrumentation were kept
outside the repository and removed/restored after the probe.

### Explicit thunk binding inside complete/incomplete handlers

To make the use-site staging visible, the same program was rerun with a named
effectful computation:

```yu
my rejected = choose::reject()
my complete_use = complete(rejected)
my incomplete_use = incomplete(rejected)
```

The CLI `check` and `dump --mono` commands both succeed. Mono output makes the
staging explicit: `m4` has type `thunk[[choose], unit]` and body
`(<effect-op choose::reject> ())`; the two uses pass `m4` as the argument to
`m3` and `m5`. Each callee body forces its argument inside
`catch marker[choose](force-thunk[…])`. The complete body has branch and reject
arms; the incomplete body has branch only.

The compiler-referee traced the runtime implementation as corroboration:
applying `Value::EffectOp` constructs `Value::Thunk(Thunk::Effect { .. })`
without requesting the effect (`crates/mono-runtime/src/runtime/flow.rs`),
and `force_thunk` emits the request (`runtime/thunk.rs`). Thus the bound
computation is a thunk passed to each function, and the displayed force occurs
under the catch marker. This closes the prior uncertainty about this exact
explicit-binding path. The later runtime probe below confirms which program
handles the request and which propagates it; this mono inspection alone does
not establish those operational outcomes. It also does not establish that the
pre-simplification weight distinction is necessary, survives type publication,
or is correctly modeled by a successor.

Both the source file and all disposable traces stayed outside the repository;
the source was removed after the CLI probes. The reviewer also corrected the
broader inference: evaluating an effect-operation expression itself
constructs a thunk rather than immediately issuing the effect, though any
other adaptation path must still be inspected before extending that claim.

### Runtime outcome of the explicit thunk pair

The exact complete/incomplete source pair above was then run with the frozen
Oracle interpreter. `complete` handles `choose::reject()` and exits 0 with no
output. `incomplete` accepts the program through inference and mono generation,
then exits 1 with `yulang.unhandled-effect` for `choose::reject`. The commands
were:

```text
yulang --no-prelude --no-cache run --interpreter /tmp/yulang-choose-complete-run.yu
yulang --no-prelude --no-cache run --interpreter /tmp/yulang-choose-incomplete-run.yu
```

An independent compiler-referee review confirms these exact operational
outcomes. Since the finalized function schemes are alpha-equivalent while the
handler bodies differ, equal schemes do not imply observational equivalence.
This is a concrete acceptance/runtime distinction between complete and
incomplete handling, but it is not an unsoundness counterexample: both programs
are accepted, and a conservative shared residual effect can coexist with the
different handler bodies. It proves neither source-to-inference adequacy,
principality, the meaning of the pre-simplification weights, nor what a
successor should erase. Under the user's priority, the successor must retain
meaningful source constraints; inference-stage scheme formatting and its
acceptance phase need not match Yulang2, while final well-typed program
acceptance remains the compatibility target. Any later erasure requires a
preservation proof.

The source files and captured outputs were temporary files under `/tmp`; no
Oracle checkout or compiler source was changed.

### Source rule behind the complete/incomplete runtime difference

Read-only inspection of `crates/infer/src/lowering/control.rs` explains the
structural source distinction. `CatchHandledEffects::is_complete` checks that
every declared operation in each handled family has an unguarded, total payload
pattern. `lower_catch_with_scrutinee` then chooses the row tail as follows:
for a complete handler it uses the handler's result-effect variable directly;
for an incomplete handler it allocates a fresh rest-effect variable. Both
constrain the scrutinee effect against the handled family row plus that tail.
Only the incomplete case also adds a direct scrutinee-effect-to-result-effect
subtype constraint. Each arm body effect flows to the same result-effect
variable. The complete `choose` fixture covers both operations, while the
incomplete fixture leaves `reject` uncovered; its `_` arm covers ordinary
values, not unhandled effect requests. This agrees with the observed runtime
outcome and explains why both sources can be accepted while only one handles
the `reject` request.

This source rule does not yet identify the pre-simplification
`AllExcept(choose)` / `All` occurrences with a particular generated row
constraint, establish whether their simplification preserves the source
effect relation, or prove a sound/principal effect interpretation. The
remaining query is to transport the actual scrutinee-effect constraints and
their derivations through row propagation, projection selection, and
specialization for each fixture. The inference-stage scheme equality is not
required by the successor; final well-typed program acceptance remains the
compatibility observation.

### Exact pass that removes the selected-view weights

A temporary Rust trace in a separate worktree at the frozen Oracle commit
captured each function's compact root immediately before and after
generalization's alias-expansion/simplification boundary. The focused command
was:

```text
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer scratch_trace_complete_incomplete_choose_roots -- --nocapture
```

For this run, complete's selected `ret_eff` included `TypeVar(28)` with
`SubtractId(0)` / `AllExcept(choose)`; incomplete's included `TypeVar(35)` with
`SubtractId(1)` / `All`. The aliases-only snapshot preserved both occurrences
and weights. The subsequent call to
`simplify_compact_root_with_role_variance_table_and_non_generic` removed each
occurrence: its substitutions list maps `TypeVar(28)` and `TypeVar(35)` to
`None`. The next snapshots have the respective residual variable (11 and 34 in
this run) shared by the argument-effect row tail and return effect, and
generalization publishes no stack quantifiers. The function schemes remain
alpha-equivalent. These numeric IDs are local to this run.

This localizes where the Oracle's formatted-scheme equality arises: selected
weights survive positive-alias expansion and are removed by the following
compact simplification. It does not prove that the removed constraints were
semantically redundant; the complete/incomplete runtime distinction remains
because the published handler bodies have different arms. Both programs still
pass Oracle check and mono generation. The disposable worktree and all trace
instrumentation were removed after capture; the frozen Oracle worktree and
repository compiler sources were not modified. Independent compiler-referee
review confirms this per-pass observation and its limits. The trace does not
isolate an internal simplification subpass, establish that all source
constraints or provenance were removed, or prove semantic preservation of the
weight erasure.

### Live source bounds on the selected weighted occurrences

A follow-up single-run Rust probe mapped each selected root and queried its
live `VarBounds` before finalization. It captured `complete = DefId(3)` at root
`TypeVar(2)` and `incomplete = DefId(4)` at root `TypeVar(31)`, removing the
cross-run ownership ambiguity. The selected `ret_eff` occurrence of
`TypeVar(28)` in the complete root has no lower bounds and three ordinary
weighted upper bounds, each to another variable (`TypeVar(14)`, `TypeVar(11)`,
and `TypeVar(9)`) with `SubtractId(0)` / `AllExcept(choose)`. The selected
`ret_eff` occurrence of `TypeVar(35)` in the incomplete root also has no lower
bounds. It has four ordinary weighted upper bounds to variables (34, 43, 40,
and 38) with `SubtractId(1)` / `All`, plus one ordinary unweighted upper
bound whose endpoint is an effect row. These are concrete live source-induced
constraint records, not only compact-root occurrences.

An independent compiler-referee review confirms the root-to-variable mapping
and exact bound shapes. The probe does not establish that these constraints
change final acceptance or are semantically necessary; their `Constraint`
derivations do not identify source spans. The successor should retain such
source constraints until a preservation argument justifies any elimination.
This follows the user's direction without making q-erasure an implementation
requirement or claiming Oracle inference-stage parity. Numeric IDs and bound
record counts are local to this fixture/run.

### Explanation provenance for those live bounds

A focused disposable Rust probe queried `why_upper_bound` for all eight upper
records on `TypeVar(28)` and `TypeVar(35)`. Every query returned
`completeness = Complete` with no truncation. The three complete-handler
weighted records each had Annotation source leaves at
`OriginId(2)/SourceBoundaryId(0)` and
`OriginId(3)/SourceBoundaryId(1)`. The four incomplete-handler weighted records
each cited `OriginId(4)/SourceBoundaryId(2)`; its unweighted row upper cited
that leaf plus `OriginId(5)/SourceBoundaryId(3)`. The explanation graphs include
weighted residual and binary replay derivations; some also contain internal
nodes, so these are the reported source leaves, not a claim that every graph
node is an annotation.

The source-path audit maps boundaries 0 and 1 to the `complete` parameter's
`x: [_] _` annotation and its generated wildcard-row subtract fact
(`SubtractFactRecordId(0)`, `SubtractId(0)`, declared `All`). Boundaries 2 and
3 map to the corresponding `incomplete` parameter annotation and generated
fact (`SubtractFactRecordId(1)`, `SubtractId(1)`, declared `All`). The annotation
constraints are lowered by `connect_lambda_pattern_annotation` through
`AnnConstraintLowerer::with_vars_and_closed_effect_rows`; wildcard facts are
registered by `effect_row_stack` / `register_stack_facts`, which allocates an
Annotation origin. This mapping follows this fixture's source/lowering order:
`SourceBoundaryRecord` retains origin and whether a location was recorded, but
not the annotation span, so boundary numbers alone do not encode source text.

An additional same-fixture trace resolves the endpoint: `NegId(13)` is
`Con(["choose"], [])`, while `NegId(58)` is `Var(TypeVar(53))`. The complete
handler's `WeightedResidual` derivation is `RowDerivationId(0)`, retaining
`NegId(13)` and citing `ConstraintRecordId(40)` plus subtract fact 0. The
incomplete handler's corresponding `RowDerivationId(1)` retains that same
`choose` family head and cites `ConstraintRecordId(94)` plus subtract fact 1.
For the complete path, record 40 is the weighted relation from the annotated
effect variable `TypeVar(6)` to a row whose head is `choose`; its left weight
is `push(SubtractId(0), All)`. This identifies the family preserved by the
row derivations and ties it to each annotation's generated subtract fact.

This still does not prove constraint necessity, establish principality or
final-acceptance impact, or show that removing the weighted occurrences
preserves behavior. The endpoint IDs and record IDs are local to this probe.

### Row-residual endpoints through root projection

A second disposable instrumentation captured the two obligations emitted by
the `WeightedResidual` row split and the compact/generalization snapshots in
the same source fixture. For `complete`, source `TypeVar(6)` creates residual
`gamma = TypeVar(28)` while retaining `choose`. The solver emits the unweighted
`TypeVar(6) <: Row([choose], gamma)` obligation, then
`gamma <: TypeVar(14)` with `push(SubtractId(0), AllExcept(choose))`. The first
obligation's generated row is `NegId(33)`; the second's tail is
`NegId(21) = Var(TypeVar(14))`. The pre-simplification compact root contains
`TypeVar(28)` as the selected weighted return-effect occurrence and contains
`TypeVar(14)` in the argument-effect row tail. After alias expansion and stack
cleanup, both the argument-effect row tail and return effect use `TypeVar(11)`;
generalization records `14 -> 11` and `28 -> None`, with quantifier 11.
This gives a structural trace across distinct artifacts: a weighted subtype
obligation reaches tail 14, a selected occurrence of 14 is substituted by
11, and the final scheme quantifies 11. Gamma 28 itself is eliminated. This
does not prove the weighted obligation causes or is necessary for quantifier
11, nor that eliminating gamma preserves the weighted relation's meaning.

For `incomplete`, source `TypeVar(35)` creates a different residual
`gamma = TypeVar(53)`, again retaining `choose`. It emits
`TypeVar(35) <: Row([choose], gamma)` unweighted, then
`gamma <: TypeVar(52)` with `push(SubtractId(1), AllExcept(choose))`.
`TypeVar(53)` is absent from the captured initial compact root; that root has
row tail `TypeVar(52)` and a selected return-effect occurrence `TypeVar(35)`
with `push(SubtractId(1), All)`. After simplification the compact root has a
closed `choose` row plus return-effect quantifier `TypeVar(34)`; substitutions
include `52 -> None` and `35 -> None`, while other selected variables 40 and
43 merge into 34. The observed split edge reaches tail 52, whose selected
occurrence is eliminated; no path from this edge to quantifier 34 was traced.
The `All` weighted occurrence on source 35 is not the
`AllExcept(choose)` residual weight on the generated split. Catch lowering
also gives incomplete coverage a fresh rest effect and a direct
scrutinee-effect-to-result constraint, while complete coverage uses the result
effect as the rest (`lowering/control.rs:961-973`). The trace therefore does
not attribute quantifier 34 to gamma 53 or this row split.

The focused Oracle command
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_trace_choose_retained_row_to_final_effect_root -- --nocapture` passed
in the disposable worktree. All temporary test/source instrumentation was
removed; the frozen Oracle checkout was unchanged. These observations close
the endpoint-to-projection mapping only for the complete path. For the
incomplete path they explicitly expose a missing causal link. Neither path
establishes row denotation, preservation, soundness, principality, or runtime
handler hygiene; the previously observed runtime difference remains explained
by differing handler-arm coverage, independently of this row-residual trace.
An independent compiler-referee delta review confirms the structural
complete-path wording and cautions that it proves neither causation nor
preservation; it also confirms that no gamma-53-to-quantifier-34 path was
captured.

### Catch result-effect route to the incomplete quantifier

A follow-up single-run lowering probe records the catch-level effect variables
before the row split. For `complete`, the scrutinee effect is `TypeVar(5)`, the
result effect is `TypeVar(14)`, and the complete handler reuses that result
effect as the row rest. The row-split obligation from gamma 28 therefore points
to the result-effect variable 14; compact generalization then substitutes a
selected 14 occurrence with quantifier 11 and removes gamma 28.

For `incomplete`, the scrutinee effect is `TypeVar(34)`, the result effect is
`TypeVar(43)`, and the row uses a fresh rest `TypeVar(52)`. The incomplete
lowering path separately emits `scrutinee.effect <: result.effect`;
generalization substitutes `43 -> 34`, and the final quantifier is 34. The
row-split edge instead sends gamma 53 to the fresh rest 52, whose selected
occurrence is eliminated. The direct scrutinee/result edge supplies the
surviving Q34 identity in this captured projection; source 35, scrutinee 34,
and gamma 53 are distinct variables. This does not rule out indirect effects
of the eliminated row split through other bound/replay paths.

The focused Oracle test
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_trace_choose_catch_result_effect_root -- --nocapture` passed in the
disposable worktree. This closes the missing endpoint mapping for this fixture.
It does not establish that eliminating gamma 28 or the fresh-rest path
preserves row meaning, nor prove soundness, principality, or runtime handler
hygiene. An independent compiler-referee delta review confirms these as
constraint/projection paths: complete's weighted edge targets result/rest 14,
whose selected occurrence becomes Q11; incomplete's direct scrutinee 34 to
result 43 edge, followed by 43 -> 34, accounts for Q34 in the captured
projection. The reviewer cautions that Q11 is already present in the initial
argument-row tail, so the complete edge's necessity is unproved, and indirect
influences of the incomplete row split were not exhaustively ruled out. Neither
path establishes row denotation, preservation, soundness, or principality.

### Minimal countermodel to dropping a shared row residual

The weighted row rule and a frozen Oracle unit test support a small
set-row countermodel to *naively deleting* a residual variable and its
obligations. Let the family universe be `{choose, other}`, fix source row
`alpha = {choose, other}`, and add two upper constraints with the same source
and row head `{choose}` but distinct tails `beta1` and `beta2`, each under
`push(s, Set({choose}))`. The rule computes
`J = {choose} ∩ Common(push(s, Set({choose}))) = {choose}` and residual weight
`push(s, Empty)`. Its obligations are:

```text
alpha <: {choose | gamma}
gamma @ push(s, Empty) <: beta1
gamma @ push(s, Empty) <: beta2
```

The row-residual key is `(source, J, residual_weight)` and excludes the target
tail, so the two constraints share one `gamma`. Under finite-set row inclusion,
the first obligation forces `other ∈ gamma`; the `take(Empty)` residual
obligations then force `other ∈ beta1` and `other ∈ beta2`. Therefore the
valuation `beta1 = beta2 = {}` has no extension to `gamma` in the original
graph. If a transformation deletes `gamma` and all three obligations without
adding equivalent projected constraints, that valuation becomes spuriously
admissible. The frozen Oracle test
`var_to_effect_row_upper_reuses_weighted_residual_for_same_source_across_tails`
passes and checks one shared residual with both tail obligations. An
independent compiler-referee review confirms the countermodel under the stated
set-row reading and emphasizes that it only refutes deletion without an
equivalent projection.

This is a countermodel to dropping the obligations, conditional on the stated
set-row interpretation. It does not show that Oracle's specific compact
simplification makes this mistake, nor a source-level acceptance mismatch.
An implementation may eliminate `gamma` only through an existential
projection that preserves the shared residual requirements for every tail.
The remaining proof task is to characterize and verify that projection for
the weighted row algebra, including row fan-out and replay, then relate it to
the root-specific gamma eliminations above.

For the isolated finite-set fragment with residual weight exactly
`take(Empty)`, the projection is explicit. Fix source assignment `A`, retained
head `J`, and target tails `B_i`, all as subsets of one finite family universe.
The split constraints are `A ⊆ J ∪ G` and `G ⊆ B_i` for every target. Then:

```text
exists G. (A ⊆ J ∪ G and for every i, G ⊆ B_i)
iff
for every i, A \ J ⊆ B_i
```

Forward: every family in `A \ J` must be in `G`, hence in every `B_i`.
Reverse: choose the least witness `G = A \ J`. This covers any finite fan-out
of one shared gamma in this restricted graph. The previous countermodel is the
instance `A={choose,other}`, `J={choose}`, `B1=B2={}`.

Independent compiler-referee review confirms the set proof and its structural
match to Oracle's emitted split/key. It requires that this lemma stay narrowly
scoped: it assumes fixed `A`, `J`, and tails in one finite set universe;
payloads, nesting, row multiplicity, right pops, filters, and other residual
weights are absent. It also assumes that `take(Empty)` acts as plain inclusion
on these tail edges. Any other lower/upper bounds, recursive occurrence, or
use of gamma require additional projected constraints. This does not prove
the Oracle compact simplifier's quantifier elimination, source final
acceptance, or principality. The next proof step is to generalize the
projection to the directed weight algebra while preserving gamma's full
constraint neighborhood and then test the general rule against root
projection.

### Authority correction from the user (2026-09-30)

The frozen Oracle's weight propagation and left/right routing are only
characterization evidence. `StackWeight`, `SubtractId`, `All`, `AllExcept(...)`,
and their current routing rules are not semantic authority and are not presumed
sound. All prior descriptions here of Oracle rules report implementation
behavior only. The finite set-row countermodel and projection lemma above are
conditional on the explicitly assumed finite-set inclusion model; neither
establishes the meaning of Yulang effects nor validates Oracle routing.

The successor must begin with a declarative effect/handler judgment
independent of the Oracle algorithm. Any retained weight representation needs
an independent meaning and a semantic preservation proof for every
left/right transformation. No weighted constraint may be erased, split,
commuted, or transferred without that proof. Counterexample search must cover
repeated pushes with one shared pop, nested frames, complete/incomplete
handlers, and residual effects. If Oracle behavior conflicts with soundness or
principality, record the exact behavior dropped, successor rule, and final
acceptance compatibility impact. Root-specific residual projection is paused
until this semantic foundation and routing derivation exist.

### Independent-semantics gate: first candidate and counterexample inventory

A read-only architecture pass recommends defining effects from source execution
before choosing a weight representation. Candidate semantic observations are
finite execution traces containing operation requests (family, operation,
payload), latent function/thunk computations, handler activations, handler
selection, and residual/unhandled requests. Function and thunk types describe
latent computations; constructing a thunk is distinct from forcing it. A
handler creates a fresh activation and handles only requests that the source
operational semantics routes to it and whose operation/payload is covered;
unmatched requests remain observable residuals. This is a candidate frame for
a judgment, not yet a complete semantics: in particular, callback provider
ownership, effectful argument mode, recursive traces, and handler eligibility
still need exact source rules.

If a weight encoding is retained, the candidate meaning should be a relation on
these semantic traces/contexts, not an interpretation borrowed from the Oracle
constructors. The proof target is: every generated left/right transformation
preserves the trace relation for every fixed outer assignment; the induced
constraint solution is least among expressible effect bounds; and function,
thunk, handler, and SCC transport are operationally adequate. An exact trace
semantics alone does not establish a finite principal inference representation.

Current explicit counterexample search has not established an unsound Oracle
routing case. Its evidence inventory is:

- Repeated pushes / one shared pop: one source callback called twice produces
two call-effect endpoints with the same `push(δ, Empty)` identity and one
frame `pop(δ)`. Each path is observed separately; the trace does not prove
that treating the paths independently or combining them is sound. A decisive
counterexample must distinguish one dynamic activation from two fresh
instantiations and compare the resulting handler observations.
- Nested frames: a concrete Oracle lowering selects an introduced outer frame
(`δ0`) while a more recently entered defined frame (`δ1`) is active. This is
implementation behavior only. Whether it is correct depends on the missing
provider/handler eligibility rule. A likely discriminating source pair is an
outer-owned callback forced beneath an inner same-family handler versus a
callback created/owned inside that inner boundary.
- Complete/incomplete handlers: a named `choose::reject` thunk is caught by a
complete handler and remains unhandled by the incomplete handler; both source
programs are accepted and their finalized function schemes are alpha-equivalent.
The runtime distinction matches arm coverage. No weight-routing conflict is
shown by this pair.
- Residual effects: deleting a shared gamma and all its edges admits an invalid
empty-tail assignment under the explicitly assumed set-row inclusion model.
Oracle itself emits the shared residual edges in the probed case. The conditional
projection lemma handles only `take(Empty)` in that model; neither result
certifies Oracle compaction or arbitrary routed weights.

The structural candidate requiring direct challenge is the separation between
lexical/provider ownership and nearest dynamic activation. Specifically, test
whether a callback whose effect provider belongs to an outer frame can be
instantiated, transported through an inner handler, and still reach the outer
handler, while an otherwise identical callback owned by the inner frame reaches
the inner handler. Then vary repeated calls, two fresh callback instantiations,
and reversed nested families. A mismatch would identify the exact routed
constraint and observable request path; until then this remains a test
hypothesis, not an Oracle counterexample or successor rule.

The next gate is to write the source-level transition/judgment rules for
provider identity, handler activation/coverage, strict versus delayed argument
execution, and residual requests. Only after that, derive any weight as a
proved encoding and search its left/right laws against this fixture matrix.
No implementation or generic residual projection follows from the current
candidate.

### Nested provider/handler routing probe

A focused frozen-Oracle CLI probe distinguishes the owner of a callback from
its dynamically active caller:

```yu
act choose:
  our branch: () -> int
  our reject: () -> never

my rejecter() = choose::reject()
my inner(f: () -> [_] _) = catch f():
  choose::reject(), _ -> 2
  _ -> 20
my outer(f: () -> [_] _) = catch inner(f):
  choose::reject(), _ -> 1
  v -> v
my inside = outer(rejecter)
inside
```

At frozen Oracle `a58eefc3`, `check` succeeds, `dump --mono` shows both inner
and outer `catch marker[choose]` sites and the thunk force under each, and
`run --interpreter --print-roots` reports root `[1]`: the outer reject arm runs,
not the inner reject arm. This is a concrete same-family provider/handler
routing observation, but not a soundness counterexample: the required
independent source rule for which activation owns this request is not yet
specified. It does refute the simplifying assumption that the nearest active
same-family handler necessarily receives every request. The paired
inner-owned callback case remains to be constructed without changing when the
callback/thunk is created or forced.

Commands, using the prebuilt frozen-Oracle binary:

```text
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-nested.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-nested.yu --mono
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-nested.yu
```

All three commands succeeded; no source/build changes were made in the frozen
checkout. The scratch source was removed after recording this result. An
independent compiler-referee review agrees that the observation is consistent
with provider-sensitive routing and is not, by itself, a routing defect.

### Paired inner-owned callback control

The missing paired source case is now characterized using two fresh temp
programs and the debug CLI built in the detached Oracle worktree. That worktree
is at frozen commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`; its only
production-source changes are the previously recorded environment-gated trace
prints in `instantiate.rs` and `selection.rs`, and no trace environment flags
were set for these runs. No repository source was changed by this probe.

The outer-owned-inline program places callback creation inside `outer`, before
calling `inner`, while both functions install a same-family `choose` handler:

```yu
act choose:
  our branch: () -> int
  our reject: () -> never

my inner(f: () -> [_] _) = catch f():
  choose::reject(), _ -> 2
  _ -> 20
my outer() = catch inner(\() -> choose::reject()):
  choose::reject(), _ -> 1
  v -> v
outer()
```

The paired inner-owned program creates and forces the callback inside the
inner handler's scrutinee:

```yu
act choose:
  our branch: () -> int
  our reject: () -> never

my inner() = catch (\() -> choose::reject())():
  choose::reject(), _ -> 2
  _ -> 20
my outer() = catch inner():
  choose::reject(), _ -> 1
  v -> v
outer()
```

Both compile through `dump --mono` and execute under the interpreter. The
outer-owned-inline version returns root `[1]`; its mono tree sends the request
through `inner` and shows the outer `choose::reject` arm as the matching
handler. The inner-owned version returns root `[20]`; its mono tree shows the
request created in the inner scrutinee and the inner catch's wildcard arm, so
the outer reject arm does not run. These results match the prior top-level
`rejecter` witness (`[1]`) and supply the missing inner-owned control.

The pair supports this characterization: the nearest dynamically active
same-family handler is not sufficient to predict the selected arm; the
callback's source/provider context affects routing. It still does **not** show
that Oracle weight propagation is unsound. The declarative source semantics
must now say how a handler activation becomes eligible for a request captured
or created by a callback, and explain both results independently of
`StackWeight` routing. The paired cases also do not yet vary repeated pushes,
instantiation, or nested effect families. The new focused commands were:

```text
/tmp/yulang-intrusion-scc-owned-target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-outer-owned-inline.yu
/tmp/yulang-intrusion-scc-owned-target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-inner-owned.yu
/tmp/yulang-intrusion-scc-owned-target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-outer-owned-inline.yu --mono
/tmp/yulang-intrusion-scc-owned-target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-inner-owned.yu --mono
```
