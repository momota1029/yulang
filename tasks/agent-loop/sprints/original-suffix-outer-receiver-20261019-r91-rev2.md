# Sprint R91 — revision 2 dependency addendum

This frozen revision 2 supersedes revision 1 only for the proof lane's read
envelope, proof output paths and aggregate budget. It preserves the exact claim,
fixture bytes, implementation lease, CLI command, semantics, exclusions and
review seam from
[`original-suffix-outer-receiver-20261019-r91.md`](original-suffix-outer-receiver-20261019-r91.md).
Revision 1's stopped result remains immutable and its 600-second grant remains
charged.

## Exact obstruction and added pins

Revision 1 stopped at `R91-SOURCE-BLOCK-1`: the fixture's braced argument needs
authentic construction of `BracedStatementBlockExpression`, while the pinned
LocalSource consumer alone cannot establish raw parser emission. Add exactly
these two read-only source owners to the proof envelope:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |

The required derivation is constructor-directed: the exact braced argument's
raw expression path selects the `LBrace` branch, constructs the statement
block, retains the `my first = signal::ping()` binding before the final
`write::ping first` expression, and feeds that authentic shape to the already
pinned LocalSource block consumer. Trace the original binder/cell, binding
scope, final expression body index and remaining saved suffix into the existing
R78/R88 runtime owners. Source order and execution/work-stack order must be
related explicitly; do not infer the construction from successful runtime
output. If another essential producer/consumer is unpinned, stop and return its
exact symbol/path without reading it.

## Revision 2 assignment and resources

After Luna verifies this addendum and the two hashes, the same proof owner
`/root/r91_proof` receives one additional 300-second grant. This is a new
sequential stage, not a reset or refund. Write only the new immutable artifacts:

- `notes/theory/2026-10-19-r91-original-suffix-outer-receiver-rev2.md`
- `tasks/agent-loop/inbox/20261019-r91-proof-rev2.md`

Read only revision 1's frozen proof/handoff, the revision 1 pinned inputs, the
two added source owners above, and the exact R78/R88 evidence named in revision
1. Do not edit revision 1 outputs. No tests/builds/CLI/probes/Git; no children.
Freeze hashes, remaining premises and a writes-stopped receipt.

Proof and implementation remain sequential under the six-slot ceiling. The
implementation worker still owns only the exact example file and only after
proof revision 2 freezes. Luna still owns the single CLI command from revision
1, only after both source outputs freeze. Fresh compiler/source and spec
reviews remain sequential after authors stop. No additional review panel is
authorized.

The original 1800-second grant is preserved, including all 600 seconds already
charged for revision 1. This addendum charges at most 120 seconds to Luna for
pin and contract administration and 300 seconds for the proof revision, raising
the aggregate cap to 2220 seconds. Existing UNKNOWN reservations remain held;
Astra remains 0.

## Unchanged claims and stop conditions

The target remains the exact source/runtime path through distinct
`signal::ping` and `write::ping` identities, resumption of the original suffix,
the outer live receiver's positive Grant, and one public `--run` result of 23.
CLI output alone proves no source correspondence or general hygiene. All six
effect-hygiene fronts remain open except for an exact reviewed finite premise
that this evidence narrows. R85 remains `AWAITING_USER_ADOPTION`; no method/role
semantics are adopted. A/B remains OPEN 0→0; R50 remains `NOT_ADOPTED`; R67,
source/native correspondence, F1/FK1, joint K,D and residual obligations remain
separate and open.

Stop on any authentic constructor mismatch, lost source order or binder
identity, a changed resumed suffix, merged effect identities, outer selection
without its positive Grant, a different CLI outcome, an unpinned essential
owner, or any need for new semantics.
