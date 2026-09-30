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

The focused test of `dump_source("pub f x = x f\n")` passed. All source and
test instrumentation was removed with the disposable worktree; the frozen
Oracle checkout remains clean. This is an observation of one lowering run,
not a durable test or a semantic proof.

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
| `V` / `E` / `C` | `TypeVar(11)` / `TypeVar(12)` / `TypeVar(13)` | application result value / result effect / call effect |
| `W` / `We` | `TypeVar(14)` / `TypeVar(15)` | wrapped returned lambda value / computation effect |

The named-self lowering allocates `S` after `R`; parameter lowering allocates
`X`. The skeleton is then reported with function value `F`, effect `Fe`, output
slots `Oe/Ov`, and body slots `Be/Bv`. Application lowering reports callee
`X`, argument `S`, and result slots `V/E/C`. The wrapper returns value `W` and
effect `We`, then installs `W <: R`. This fixes the role correspondence for
the symbolic constraint list in
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

The trace did not print the exact role mapping for every effect occurrence,
all `Eff(_)` bounds, the complete constraint/event epoch, or the selected
`CompactRoot`/rewrite/final-scheme correspondence. In particular, `Oe` and
the application call-effect slot occur in stack-weighted endpoints; their
identity relationship is governed by subtraction evidence, not assumed to be
plain equality. Those are still required for the source-to-scheme theorem.

No compiler code in this branch changed. The only test was the focused
temporary Oracle trace above; no broad suite or performance measurement ran.
