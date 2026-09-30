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
selected compact view equals a candidate `H_d`, or connect its two
quantifiers and zero sandwiches through polarity rewrite to the public scheme.
The q upper/lower evidence, latent stack relation, selected-root observation,
and final use relation remain separate obligations. The instrumentation was
discarded with the disposable worktree; frozen Oracle remains clean.

The follow-up effect-role trace printed the callee and argument computation
effects and the lambda parameter effect slots. Together with the earlier
skeleton and wrapper trace, it resolves every named effect variable in the
symbolic inventory and confirms the parameter's Bottom slot. It does not
resolve the complete constraint/event epoch or the selected
`CompactRoot`/rewrite/final-scheme correspondence. In particular, `Oe=5` and
the application call-effect `C=13` occur in stack-weighted endpoints; their
relationship is governed by subtraction evidence, not assumed to be plain
equality. Proving that relation through the selected-root and scheme stages
remains required for the source-to-scheme theorem.

No compiler code in this branch changed. The focused source-map and root
preparation scratch tests ran only in disposable Oracle worktrees; no broad
suite or performance measurement ran.
