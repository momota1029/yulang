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

## Consequence for the full redesign goal

The effect-free Function graph in the abstract-semantics draft can serve as a
component lemma only. It cannot be the end-to-end source envelope or the
acceptance boundary for the user's Oracle-capability objective. The successor
semantics must eventually account for latent effect bounds, forced
generalization, use-site freshening, preserved shared identities, and the
sequential root/publication lifecycle. Handler matching, masks, weights, and
runtime freshness remain separate obligations until the supported source
envelope says they are admitted.

No Oracle code was changed and no test or measurement was run for this record.
The frozen source paths and prior focused probe records above are the evidence.
