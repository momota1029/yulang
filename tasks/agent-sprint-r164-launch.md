# R164 source/proof launch and active-work receipt

Session: `EFFECT-PERMISSION-ORIGINAL-TYPED-UNION/20261102-R164`
Contract revision 2 SHA-256: `fbd0895f1cb48f1741ac8c438659dab32d2133c48291df833bbcd35aa439db48`.
Revision 2 added source-contracts §2.1 after the Lean worker acknowledged the
new governing input.
Baseline: `0134bbdc767db45abcbec35182c0c317de4c3b59`; admission checkpoint
`3247451a7` is pushed.

At 2026-11-01 06:25 UTC, the live roster was synchronized. It showed the
primary and the actual Lean worker `/root/r164_typed_union_lean` running; all
previous R163 workers were completed. The Lean worker acknowledged its exact
packet and confirmed it will not introduce a relation before consuming the
frozen Luna source intake. No old UNKNOWN assignment was reconciled or released.

| Actual owner | Requested work | Exact output paths |
|---|---|---|
| `/root` | Luna source intake, max 1200 sec | `notes/theory/2026-11-02-original-typed-union-r164.md`; `tasks/agent-loop/inbox/effect-permission-original-typed-union-r164-source.md` |
| `/root/r164_typed_union_lean` | `lean_prover`, Sol/high, max 600 sec | `notes/theory/lean/YulangClosure/OriginalTypedUnionR164.lean`; `tasks/agent-loop/inbox/effect-permission-original-typed-union-r164-proof.md` |

Observed model/effort for the worker are UNKNOWN. This receipt records the live
session and actual launch/acknowledgement. The fixed aggregate budget is 2700
seconds; Astra budget is 0. Rust source has no lease; any scoped Rust delta is
conditional on an authentic supplier and primary adjudication.
