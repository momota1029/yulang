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
