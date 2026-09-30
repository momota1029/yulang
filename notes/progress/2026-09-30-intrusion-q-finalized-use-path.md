# Q fixture: finalized scheme use path

Date: 2026-09-30  
Status: source-audited Oracle path; no source/use equivalence claim  
Scope: frozen Yulang2 Oracle at `a58eefc31`, ordinary instantiation after
generalization of `pub f x = x f`

## Distinguish the recursive self-reference from an incoming scheme use

In `pub f x = x f`, the `f` in the body is a live named-self value used while
lowering the definition. The source-lowering inventory records no
`SccEvent::OpenUse` for this fixture. That occurrence is not an ordinary
incoming use of the finalized scheme. The public result records successful
generalization, formatted type `any -> ['a] 'b`, two ordinary quantifiers,
and no surviving recursive bounds; the q row observed during compaction is
therefore not part of the scheme interval reinstalled for this member. See
`2026-09-30-intrusion-powerset-carrier-candidate.md:198–207,758–774`.

The ordinary post-publication path is separate:

1. `quantify_component` collects the generalized component, then finalizes
   each member and calls `set_def_scheme`; see frozen
   `crates/infer/src/analysis/session/instantiate.rs:14–82` and
   `analysis/session/generalize.rs:958–963`.
2. A later `UseResolved` event enters `instantiate_use_batch` and
   `prepare_instantiated_use`; the latter requires a published
   `Def::Let { scheme: Some(..) }` (`analysis/session/instantiate.rs:311–369`).
3. For an ordinary local scheme, the path calls
   `instantiate_scheme_with_roles_and_provenance` with the secondary type
   level and witness inputs (`analysis/session/instantiate.rs:383–455`). A new
   `SchemeInstantiator` is created for each call (`instantiate.rs:81–96,
   516–528`).
4. One per-use TypeVar map freshens ordinary quantifiers and surviving
   recursive binders, then clones the predicate and role constraints; free
   TypeVars without a map entry retain their identity (`instantiate.rs:620–648,
   732–761`). Stack identities use a separate map and unmapped stack identities
   remain shared (`instantiate.rs:741–767`). Pos/Neg/Neu DAG cloning preserves
   within-use sharing, including Function value/effect positions and stack
   weights (`instantiate.rs:788–999`).
5. Only surviving recursive rows add lower/upper subtype constraints for their
   fresh binders (`instantiate.rs:1002–1030`). The published `f` has no such
   rows, so this path does not reinstall q's recursive interval.
6. The cloned predicate is attached to the incoming `use_value`, with the
   implementation choosing direct lower insertion for a structural top-level
   constructor and subtype insertion otherwise; role constraints follow
   (`analysis/session/instantiate.rs:505–524,717–729`). The batch commits its
   queued edges at `:325–335`.

These source facts explain the ordinary-use identity policy; fixture-specific
scheme and use observations follow below. They do not prove the q
rewrite/prune or source-to-scheme theorems.

## Two incoming-use probe

A temporary Rust characterization test first used two unconstrained incoming
uses, then replaced their definitions with annotations to force distinct
result types. The final discriminating source was:

```text
pub f x = x f
pub use_int: int = f 1
pub use_bool: bool = f 2
```

It ran in the disposable Oracle worktree at `a58eefc31`, with temporary
environment-gated tracing in `instantiate.rs` and
`analysis/session/instantiate.rs`. Command:

```text
YULANG_INTRUSION_USE_TRACE=1 YULANG_TRACE_SCHEME_DEFS=0 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qscheme-use-target \
  cargo test -p infer --lib scratch_intrusion_q_scheme_two_uses -- --nocapture
```

Result: 1 passed. The finalized scheme is recorded exactly as:

```text
quantifiers: [TypeVar(8), TypeVar(13)]
stack_quantifiers: []
recursive_bounds: []
predicate: Fun {
  arg: Top,
  arg_eff: Bot,
  ret_eff: Var(TypeVar(13)),
  ret: Var(TypeVar(8)),
}
```

Both later references resolve to target `DefId(0)` and enter the ordinary
scheme path. The first use (`parent DefId(1)`, `use_value TypeVar(17)`) maps
the quantifiers to `TypeVar(32)` and `TypeVar(33)` and attaches `PosId(36)` by
the `direct-lower` route in the unannotated probe. In the final annotated run,
the first use maps them to `TypeVar(32)` and `TypeVar(33)` and attaches
`PosId(39)`; the second (`parent DefId(2)`, `use_value TypeVar(25)`) maps them
to `TypeVar(34)` and `TypeVar(35)` and attaches `PosId(42)`. Both use the same
`direct-lower` route. The resulting public bindings format as `int` and
`bool`, respectively, with no lowering errors. Thus the dump reports distinct
result types for this captured pair of ordinary incoming uses, and the two
quantified type identities are fresh and disjoint across these two use calls.
This particular scheme has no unmapped type or stack identity in its predicate,
so it does not test shared
outer anchors. It has no stack quantifier or recursive bound; consequently
there is no per-use stack freshening or q-row reinstallation in this fixture.

In the earlier unannotated run each call received eleven witness inputs. The
projection retained four mappings (two root mappings and two argument
mappings); seven structural witnesses remained incomplete. The annotated
run did not change or fully re-audit those provenance mappings. Neither run
tests shared outer anchors. The annotated observations constrain result types,
not the quantified latent return-effect identity, and the partial witness
projection is not a provenance-preservation proof. Temporary instrumentation
and the scratch test are uncommitted changes in the disposable Oracle
worktree; they are not part of frozen commit `a58eefc31`.

## Concrete-use specialization of `f 1`

The inference-stage two-use result is not an end-to-end specialization result.
On frozen Oracle commit `a58eefc31`, this source:

```text
pub f x = x f
pub main = f 1
```

fails the mono dump route. From `/tmp/yulang-intrusion-oracle`, the command
`target/debug/yulang dump-mono /tmp/yulang-intrusion-q-runtime-probe.yu`
exits 1 with:

```text
compile error [yulang.unsatisfied-subtype]:
unsatisfied subtype constraint: int <: 'open0 -[[], 'open2]-> 'open1
```

The source path explains why specialization revisits the body. A temporary
trace in the disposable frozen-Oracle checkout records the exact instance:

```text
enqueue def=DefId(0) signature=Fun {
  arg: Con { path: ["int"], args: [] },
  arg_effect: EffectRow([]), ret_effect: EffectRow([]),
  ret: Con { path: ["unit"], args: [] }
}
solve id=InstanceId(1) def=DefId(0) signature=Fun { ...same... }
```

This is the `f` instance at `int -> unit`, not merely a possible explanation.
The trace confirms that this use signature reaches the definition-body check
that rejects `int <: Function`. In
`specialize2/emit.rs::emit_var`, a local definition reference obtains its
per-use `solved.ref_signature(expr)` and passes that signature to
`ensure_def_instance`. The instance queues this as `inference_signature_ty`;
`drain_pending_instances` passes it to `TaskSolver::solve_def_body`. That
solver rechecks the definition body under the per-use signature via
`expr_with_signature`, consumes the body against that signature, and adds the
materialized subtype obligation before finishing
(`specialize2/task_solver.rs::solve_def_body`). The captured signature has
argument `int`; the body uses that parameter as a callee and produces the
observed `int <: Function` failure. Therefore the inference-stage `Top`
argument does not make this concrete use succeed end to end.

This characterizes this concrete two-stage use, not whether all uses that
violate an erased recursive bound are rejected, nor runtime behavior.
The standard `check` and `run` routes on this exact self-application source
did not finish within the observation window and were interrupted; their
terminal behavior remains unknown. No frozen Oracle source or test was
modified.

## Function-valued incoming use

A second disposable source probe changes only the incoming argument:

```text
pub f x = x f
pub id x = x
pub use id = f id
```

`dump-mono` rejects this source too. The temporary instance trace records the
`f` instance signature as `(unit -> unit) -> unit` and the `id` instance as
`unit -> unit`. The diagnostic is
`(unit -> unit) <: unit`, located at the recursive `f` occurrence in the body
of `f`. Given those signatures, this is the expected conflict: the argument
`id` is used to call the recursive value `f`, while this instance of `id`
expects its argument to be `unit`. This is a second concrete use whose
inference-stage generalized view does not imply end-to-end acceptance.

This probe used the same temporarily instrumented binary as the `f 1` trace,
with tracing enabled only for the command. It is an observed mono-specializer
result for this source, not a general proof that specialization reconstructs
every erased recursive constraint or that an intrusion solver has the same
accepted-use relation.

## Shared outer anchor with two local scheme uses

A second disposable-worktree Rust probe used:

```text
my outer x =
  my inner y = ({left: x, right: x}, y)
  (inner 1, inner 2)
```

The local `inner` scheme formats as `'a -> ({left: 'b, right: 'b}, 'a)`.
It has one quantified identity, `TypeVar(10)`, while the traced `x`
occurrences use free `TypeVar(2)`. Each of the two local uses targets
`DefId(2)`. The first creates use value `TypeVar(27)`, maps the quantified
identity to `TypeVar(28)`, and clones the unmapped `TypeVar(2)` to itself. The
second creates use value `TypeVar(35)`, maps the quantifier to `TypeVar(36)`,
and again clones `TypeVar(2)` to itself. This establishes independent local
identity freshening and a shared identity at the clone operation for these two
local uses.

The outer binding formats as
`'a -> (({left: 'a, right: 'a}, int), ({left: 'a, right: 'a}, int))`; the
dump shows the same outer parameter `x` in both returned record pairs. This is
an accepted source fixture with no lowering errors. These are local block
uses through `instantiate_local_value` and the subtype-route path, not the
earlier top-level `UseResolved` direct-lower path. Both arguments are integers,
so this does not show distinct local choices under later constraints. The
trace also does not print a raw instantiated predicate or the complete
post-constraint graph, and does not prove general contextual preservation,
effect behavior, diagnostics/provenance equality, or q-erasure.

Command:

```text
YULANG_INTRUSION_USE_TRACE=1 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qscheme-use-target \
  cargo test -p infer --lib scratch_intrusion_q_scheme_two_uses -- --nocapture
```

Result: 1 passed. Temporary changes remain uncommitted in the disposable Oracle
worktree and are not part of frozen commit `a58eefc31`. Independent
compiler-referee review checked the source, trace, and limits; it found no
blocking or major issue.

## Effect-sensitive incoming-use trace

A follow-up disposable-Oracle probe places two calls to `f` in differently
typed handlers:

```text
pub act ask 'a:
    pub get: () -> 'a
pub answer_int(action: [ask int] _) = catch action:
    ask::get(), k -> answer_int(k 1)
    v -> v
pub answer_bool(action: [ask bool] _) = catch action:
    ask::get(), k -> answer_bool(k true)
    v -> v
pub f x = x f
pub use_int: int = answer_int: f 1
pub use_bool: bool = answer_bool: f true
```

The focused `dump_source` characterization asserted no lowering errors and
passed. In this fixture `f` is `DefId(4)`. Its finalized raw predicate again
has `ret_eff = Var(TypeVar(83))`, quantified alongside the result `TypeVar(78)`.
The `use_int` incoming use (`parent DefId(5)`) maps TypeVar83 to TypeVar115;
the `use_bool` use (`parent DefId(6)`) maps it to TypeVar119. The two distinct
fresh effect identities each receive an upper bound through their respective
application constraints. The bounded variable trace then shows the int path
reaching an upper row `ask(NeuId(5))` with tail TypeVar113, while the bool path
reaches `ask(NeuId(7))` with tail TypeVar117. The source annotations identify
these handler contexts as `[ask int]` and `[ask bool]`. Both scheme predicates
are attached by the direct-lower route.

Command:

```text
YULANG_INTRUSION_USE_TRACE=1 YULANG_TRACE_SCHEME_DEFS=4 \
  YULANG_TRACE_VAR_BOUNDS=94,95,107,108,113,115,117,119 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qscheme-use-target \
  cargo test -p infer --lib scratch_intrusion_q_scheme_effect_uses -- --nocapture
```

Result: 1 passed. The trace is captured at
`/tmp/yulang-intrusion-effect-use.log`. An independent compiler-referee audit
confirmed the identity mapping and identified the limit: the capture does not
show fully normalized effects, all handler subtraction edges, or a semantic
assertion that the two complete effect-choice sets remain independently
observable. Therefore this establishes distinct quantified `ret_eff`
freshening and distinct context rows in the captured constraint graph, not
solved-effect independence, general contextual preservation, provenance or
diagnostic equality, or q-erasure preservation.

## Next proof obligation

Trace each fresh `ret_eff` through handler subtraction and to a final normalized
effect observation, or add a semantic assertion that distinguishes shared from
independent effect choices. Then state the exact `Obs_scheme` relation for
those uses, including type result, latent effects, diagnostics, and exposed
provenance. Keep this separate from the unproved pre-view `q` rewrite/prune
preservation theorem and from the source-generated constraint graph's
regular-presentation correspondence.

The source-path mapping above was read-only. Subsequent disposable-worktree
Rust probes modified only the temporary Oracle checkout and ran the focused
scratch tests recorded above; no Oracle commit or repository source was
changed. Compiler-referee reviews checked the q-use, shared-anchor, and
effect-sensitive traces against their captures and source. Their scope was
these fixtures, not the q-projection or intrusion theorem.

## Distinct effect-family follow-up

A further temporary source fixture uses the same polymorphic `f` at two
independent incoming uses, one under a complete `ask` handler and one under a
complete `tick` handler. The focused Oracle scratch test passes with no
lowering errors. Its scheme trace maps `f`'s quantified return-effect
`TypeVar(17)` to distinct use identities `TypeVar(83)` and `TypeVar(86)`.
The bound dump gives the first identity lower rows formatted `[ask 'a]` and
the second a lower row `[tick]`; the source callbacks and handler clauses use
those respective families. Catch construction records separate scrutinee and
result effect variables (`35 -> 38` and `66 -> 69`) and complete handled rows.

This strengthens the fixture from distinct context parameters to distinct
effect-family constraints. It still does not establish that each handler
consumes its matching row, that the other family's row is preserved or
excluded, or what normalized final effect each use exposes. The temporary
row-reduction instrumentation emitted no matching reduction event, so no
consumption claim follows from this run. Independent compiler-referee review
also found the ask/tick rows among lower bounds of the catch result-effect
variables, which are connected to their scrutinee effects. Since the handler
continuations resume with `k`, this alone neither proves a leaked effect nor
proves consumption. A follow-up must capture reduction/subtraction for each
scrutinee-to-handled-row constraint, including row tails, and assert or print
the final catch effects under the intended continuation semantics before this
can count as effect-choice independence.

Command:

```text
YULANG_INTRUSION_USE_TRACE=1 YULANG_INTRUSION_EFFECT_TRACE=1 \
  YULANG_TRACE_SCHEME_DEFS=2 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qscheme-use-target \
  cargo test -p infer --lib scratch_intrusion_q_effect_caught_uses -- --nocapture
```

Result: 1 passed. Capture:
`/tmp/yulang-intrusion-distinct-effects-replay.log`. All temporary Oracle
instrumentation and the scratch test were restored; the frozen checkout is
clean at `a58eefc31e22141574b6f20c6a5748151c6d79f1`.

## Non-resuming distinct-family observation

To make each handled effect independently observable without resuming its
continuation, a follow-up fixture wraps the catches in exported functions:

```yu
pub act ask 'a:
    pub get: () -> 'a
pub act tick:
    pub ping: () -> bool
pub f action = action ()
pub use_int = \() -> catch f (\() -> ask::get()):
    ask::get(), k -> 1
    v -> v
pub use_bool = \() -> catch f (\() -> tick::ping()):
    tick::ping(), k -> true
    v -> v
```

The focused Oracle scratch test passes with no lowering errors. Instrumented
instantiation maps `f`'s quantified variables `(TypeVar(11), TypeVar(17))`
to `(80, 81)` at one use and `(83, 84)` at the other, so the two incoming
uses do not share the callback's latent effect identity. Initial row reduction
consumes the matching `ask` item at TypeVars 31 and 32 and the matching `tick`
item at TypeVars 61 and 62, each with empty residual. Late-lower replay also
consumes `ask` with empty residual at TypeVars 31 and 32.

The raw finalized output schemes for `use_int` and `use_bool` have no
quantifiers, and their Function predicates use `ret_eff = Bot`. The compact
schemes print `() -> int` and `() -> bool`. The formatter prints an unknown
positive effect variable by name, so these published positive schemes do not
hide a live effect variable. Independent compiler-referee review confirmed
that this closes the prior fixture's missing tick-reduction and exported-effect
observations.

Scope remains fixture-local. Positive `Bot` is a lower/bottom effect, not a
closed empty-row upper bound on internal catch result variables (TypeVars 39
and 69); those live variables still have lower bounds and no upper bounds in
the capture. Therefore this does not establish normalized purity along every
internal path or general `Obs_scheme`, arbitrary handler preservation, q
rewrite/prune preservation, or diagnostic/provenance equality. The next proof
work returns to the selected-bound graph/q-erasure bridge and the remaining
source-to-scheme relation; retain the internal-effect caveat.

Command:

```text
YULANG_INTRUSION_USE_TRACE=1 YULANG_INTRUSION_EFFECT_TRACE=1 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qscheme-use-target \
  cargo test -p infer --lib scratch_intrusion_q_caught_nonresuming_effects -- --nocapture
```

Result: 1 passed. Capture: `/tmp/yulang-intrusion-nonresume-initial.log`.
The reviewer also inspected raw finalized schemes in that capture and the
formatter/reduction implementation. All temporary Oracle instrumentation and
the scratch test were restored; the frozen checkout is clean at
`a58eefc31e22141574b6f20c6a5748151c6d79f1`.
