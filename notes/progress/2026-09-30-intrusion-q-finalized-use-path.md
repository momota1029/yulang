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

## Next proof obligation

Construct an effect-sensitive incoming-use context for the quantified latent
return-effect identity. Trace its scheme-instantiation constraints and final
observations to show that local effect choices stay independent. Then state
the exact `Obs_scheme` relation for those uses, including type result, latent
effects, diagnostics, and exposed provenance. Keep this separate from the
unproved pre-view `q` rewrite/prune preservation theorem and from the
source-generated constraint graph's regular-presentation correspondence.

The source-path mapping above was read-only. Subsequent disposable-worktree
Rust probes modified only the temporary Oracle checkout and ran the focused
scratch tests recorded above; no Oracle commit or repository source was
changed. A compiler-referee reviewed the q-use trace and shared-anchor delta in
two scoped passes against the captures and source. The review found
documentation wording issues that were corrected. Its scope was these
fixtures, not the q-projection or intrusion theorem.
