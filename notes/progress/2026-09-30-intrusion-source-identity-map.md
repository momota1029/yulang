# Intrusion source identity map for `pub f x = x f`

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: fixture-local lowering identity observation; no simulation theorem

## Capture

A disposable worktree at the frozen Oracle commit added trace-only output to
named-self binding setup, defined-lambda skeleton construction, and application
lowering. It ran:

```text
CARGO_TARGET_DIR=/tmp/yulang-intrusion-source-map-target \
  cargo test -p infer --lib scratch_source_map_self_application -- --nocapture
```

The focused test of `dump_source("pub f x = x f\n")` passed. A follow-up run
used the same command with test name
`scratch_source_effect_role_map_self_application` and additional logging of
callee/argument effects and parameter effect slots; it also passed. All source
and test instrumentation was removed with the disposable worktree; the frozen
Oracle checkout remains clean. These are observations of one lowering shape,
not durable tests or semantic proofs.

## Exact value-identity map

The source lowering trace resolves the symbolic variables in the earlier
`Csrc` inventory:

| Symbol | Oracle identity | Source role |
|---|---:|---|
| `R` | `TypeVar(0)` | public definition root |
| `S` | `TypeVar(1)` | local named-self value for `f`; `DefId(0)` in this run |
| `X` | `TypeVar(2)` | defined-lambda parameter `x` |
| `F` | `TypeVar(4)` | one-layer defined-lambda skeleton function value |
| `Fe` | `TypeVar(3)` | skeleton function computation effect |
| `Oe` / `Ov` | `TypeVar(5)` / `TypeVar(6)` | skeleton output effect / value |
| `Be` / `Bv` | `TypeVar(7)` / `TypeVar(8)` | skeleton body effect / value |
| `Ec` / `Ea` | `TypeVar(9)` / `TypeVar(10)` | callee `x` / argument `f` evaluation effects |
| `V` / `E` / `C` | `TypeVar(11)` / `TypeVar(12)` / `TypeVar(13)` | application result value / result effect / call effect |
| `W` / `We` | `TypeVar(14)` / `TypeVar(15)` | wrapped returned lambda value / computation effect |

The named-self lowering allocates `S` after `R`; parameter lowering allocates
`X`. The skeleton is then reported with function value `F`, effect `Fe`, output
slots `Oe/Ov`, and body slots `Be/Bv`. Application lowering reports callee
`X/Ec`, argument `S/Ea`, and result slots `V/E/C`. Both `Ec` and `Ea` come
from unannotated local names whose local effect slot is exact-pure. The
unannotated parameter has `arg_eff = skeleton_arg_eff = NegId(0)`, the Bottom
effect slot rather than another effect variable. The skeleton function effect
`Fe` and returned-lambda computation effect `We` are also allocated by the
exact-pure helper. The wrapper returns value `W` and effect `We`, then installs
`W <: R`. This fixes the role correspondence for the symbolic constraint list in
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`.

The independently captured q-cycle identities now join this map directly:
`q = X⁻ = TypeVar(2)⁻` and `y = S⁺ = TypeVar(1)⁺`. The selected application
bound is therefore the parameter constraint whose source application is
`x f`; the cycle's other selected edge is a replay-derived lower rooted in the
defined-lambda/self constraints. This identifies the vertex roles, but does
not make the replay record a direct source constraint or prove that the
collector's transient recursive row is an independent inequality.

## Origin and limits

The skeleton predicate connection is observed with `OriginId(1)` and the
application call with `OriginId(2)`. The previous source-boundary trace maps
`OriginId(2)` to `SourceBoundaryId(0)` and application bytes `10..14`.
Constraint `BoundRecordId(7)` is the direct application upper on `X`; the q
cycle's `BoundRecordId(4)` remains a replay conjunction at `TypeVar(4)` with
premises rooted at unknown-internal constraints. This run-level ID alignment
does not establish stable numeric identities across runs.

## Root-preparation attempt for this fixture

A second disposable worktree added trace-only epoch/restart logging to
`generalize_root_with_prepasses_and_metrics` and ran the exact source through
the production dump path:

```text
YULANG_INTRUSION_EXACT_ROOT_TRACE=1 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-root-epoch-target \
  cargo test -p infer --lib scratch_exact_root_epoch_self_application -- --nocapture
```

The focused Rust test passed. For `DefId(0)` / `R=TypeVar(0)`, root
preparation began at `ConstraintEpoch(27)`. It completed one attempt: the root
compaction returned at epoch 27 with zero merge constraints; no merge,
subtype, cast, or role restart occurred; both post-alias and post-cleanup
companion passes reported `changed=false` at epoch 27. The saved generalized
root had two ordinary quantifiers and zero recursive sandwiches. These IDs
and counts describe that captured run only.

The source identity map and this root-attempt log came from separate runs.
Their shared `DefId(0)` / `TypeVar(0)` labels are run-local correspondences
for the same first source definition, not persistent identity claims.

This establishes that this source fixture's *root preparation* is a single
non-mutating attempt once it starts at epoch 27. It does not trace the earlier
source constraint/event construction that reached that epoch, prove the
selected compact view equals a candidate `H_d`, or prove q-erasure preserves
the source relation. A later capture below connects the generalized compact
representation to the final raw scheme. The q upper/lower evidence, latent
stack relation, selected-root observation, and final use relation remain
separate obligations. The instrumentation was discarded with the disposable
worktree; frozen Oracle remains clean.

## Generalized compact root to finalized scheme

A third disposable Oracle worktree logged the returned `GeneralizedCompactRoot`
and the scheme immediately before and after `finalize_generalized_compact_root`
for this same exact source. The focused Rust dump test passed. The generalized
root's compact Function is:

```text
arg      = CompactType { vars: [], ... }                 // finalized as Top
arg_eff  = CompactType { never: true, ... }               // finalized as Bot
ret_eff  = Var(TypeVar(13)), weight Empty, origin Secondary
ret      = Var(TypeVar(8)),  weight Empty, origin Secondary
rec_vars = []
```

Its quantifiers are `[TypeVar(8), TypeVar(13)]`, with no stack quantifiers,
roles, or recursive sandwiches. The substitution table maps application
result `V=TypeVar(11)` to `TypeVar(8)`; source q `X=TypeVar(2)` has no target
and is absent from the compact root/recursive table. The finalized raw scheme
preserves these fields exactly: quantifiers `[8,13]`, no recursive bounds or
stack quantifiers, and predicate `Fun(arg=Top, arg_eff=Bot,
ret_eff=Var(13), ret=Var(8))`, formatted `any -> ['a] 'b`.

The role names are inferred by joining this capture with the separate source
identity trace for the identical source text: `TypeVar(8)=Bv` and
`TypeVar(13)=C`. The same numeric IDs were observed independently in the two
captures, but remain run-local labels, not persistent identities. The direct
capture establishes the final compact-to-scheme representation map and confirms
that q's transient row does not
appear in this finalized scheme. It does **not** establish that dropping q
preserves `Obs_source`/`Root_d`/`Pred_d`, that the transient pre-projection row
is only a back-reference, or that the stack subtraction makes `C` the right
public effect representative.

Command:

```text
YULANG_INTRUSION_PROJECTION_TRACE=1 YULANG_TRACE_SCHEME_DEFS=0 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-projection-target \
  cargo test -p infer --lib scratch_exact_projection_self_application -- --nocapture
```

All instrumentation and the scratch test were discarded with that worktree;
the frozen Oracle checkout remains clean.

## Polarity rewrite and recursive-row pruning stages

A fourth disposable Oracle worktree traced `eliminate_polar_variables_with_roles_and_non_generic`
and `prune_unreachable_recursive_bounds` for the same source. Its focused
Rust dump test passed. The captured stage data shows:

1. Before polarity rewrite, the root Function argument contains the primary
   `TypeVar(2)` q occurrence and `rec_vars` contains q's interval.
2. The rewrite returns a substitution for `TypeVar(2)` with `target=None`;
   the rewritten root's Function argument has no variables, while the copied
   recursive table still contains q and its interval.
3. Before reachability pruning, the root argument remains empty and the q row
   is still present. After pruning, `rec_vars=[]`.
4. The final `GeneralizedCompactRoot` capture above agrees on the root shape,
   no q recursive row, and no recursive sandwich; finalization emits no
   recursive bound.

### Operational pruning lemma for this one-row case

Let the post-rewrite state be a root `T`, roles `P`, and exactly one
recursive row for q. If q is absent from the free variables of `T` and `P`,
`prune_unreachable_recursive_bounds` removes that row. Its reachability set
starts with `FV(T) ∪ FV(P)`. The closure loop can visit the q row only if q is
already in that set; since there are no other rows, the loop cannot add q.
The final retain keeps only rows whose variable is in the resulting closure,
so q is discarded. The captured fixture satisfies these premises: the
polarity rewrite removes q from the root, there are no reachable role rows,
and the saved recursive table initially has only q. This proves the *code's
reachability-prune result* for this captured shape; it says nothing about
whether removing q preserves typing or principal observations.

The trace also shows that polarity rewrite does not finish the whole compact
view: the intermediate Function result still has two `SubtractId(0)`-weighted
value occurrences. The separate final-root capture has one unweighted result
variable after later cleanup/substitution. The captures use run-local IDs;
the exact semantic role of those transformations still needs proof.
Therefore this closes the operational `q -> None; retain row; prune row`
stage order for the fixture, not the `Obs_source`-preservation theorem or the
meaning of the collector's transient q row.

Command:

```text
YULANG_INTRUSION_QPROJECTION_TRACE=1 \
  CARGO_TARGET_DIR=/tmp/yulang-intrusion-qprojection-stages-target \
  cargo test -p infer --lib scratch_qprojection_stage_self_application -- --nocapture
```

The trace emitted multiple rewrite calls on compact copies during this root's
pipeline. The sequence above states only the repeated local rewrite/prune facts;
it does not claim every emitted snapshot is one uninterrupted mutation chain.
Instrumentation and the test were discarded; frozen Oracle remains clean.

The follow-up effect-role trace printed the callee and argument computation
effects and the lambda parameter effect slots. Together with the earlier
skeleton and wrapper trace, it resolves every named effect variable in the
symbolic inventory and confirms the parameter's Bottom slot. It does not
resolve the selected `CompactRoot` to `GeneralizedCompactRoot` semantic
adequacy, complete source constraint/event construction, or public use
observations. In particular, `Oe=5` and the application call-effect `C=13`
occur in stack-weighted endpoints; their relationship is governed by
subtraction evidence, not assumed to be plain equality. Proving that relation
through the selected-root and scheme stages remains required for the
source-to-scheme theorem.

No compiler code in this branch changed. The focused source-map and root
preparation scratch tests ran only in disposable Oracle worktrees; no broad
suite or performance measurement ran.
