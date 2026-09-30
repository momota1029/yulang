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
endpoint with `StackWeight::push(δ, Empty)` (`tail.rs:769–796`). Thus the
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
