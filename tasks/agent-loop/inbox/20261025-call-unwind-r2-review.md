# Independent review: Call request/failure unwind r2

**CLEAN — no BLOCKING, major, or minor findings** within
`LEAN-CALL-UNWIND-20261025/r2`.

Reviewer: `/root/call_unwind_r2_review`; requested model/effort
`gpt-6.1-sol/medium`, observed `UNKNOWN/UNKNOWN`. Review was read-only and
independent of the authors. The reviewer sent the complete receipt to Luna
because its governing role prohibited filesystem writes; Luna transcribed it
only after the reviewer STOPPED and the report lease transferred.

## Proposition and construction audit

The change repairs the actual r1 elaboration cause. Before destructing `s`,
both corollaries explicitly normalize preservation equalities through the
definitional projections of `CallState.initial`. The endpoint result/suffix
conjuncts use those normalized equalities. Comparison with the failed
candidate shows only these two bridges and their four uses changed; theorem
statements, premises, quantifiers, and endpoints are unchanged.

Independent source inspection covered `Contracts.Prefix`,
`ControlSyntax.Metadata`, initial state, `captureBind`, `contextControlFrame`,
every request/failure constructor and finalizer, `ControlTyping.CallStateTyped`,
accepted finite preservation and terminal typing, all three submitted
modules, and the relevant operational bind/scope/expose clauses. Producer
handoffs were read after source inspection and were not used as correctness
evidence.

- Request capture processes the innermost frame first. Bind and adapter use
  the actual response-binder lifting operation. Scope and expose retain the
  correct syntax, effect/result order, world operations, and scope changes.
  Final `viewContext` is `observed`.
- Failure induction obtains each cleanup witness from `md.failWorld_total`
  with the exact frame mapping. All four constructors are covered; only Call
  frames are consumed. The final world remains existential.
- `call_prefix_append` follows the actual snoc-oriented relation and gives
  `n + m`, including either zero-length prefix. Both corollaries concatenate
  the supplied initial prefix with the constructed unwind segment, preserving
  exactly `n + (s.frames.length + 1)`.
- Request terminal typing retains the same operation's payload type and
  response binder, with continuation result `t.resultType`. Outer
  `Control.Ty result` remains distinct from `Original.Ty`.
- Every endpoint conjunct matches the frozen contract. There is no request
  scope equality or endpoint world equality. Failure retains scope/view/
  receipt fields precisely as the existing constructors do.
- No reachability, cleanup correctness, lifecycle restoration, source/native,
  original Call A/B, inference A/B, or production closure follows or is
  claimed.

## Evidence audit

| Artifact | SHA-256 |
|---|---|
| r2 contract | `4847f89672c8821df47d9ed2e1162b150b3b578b4aec8304e6d2331389c27c01` |
| repaired source | `1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3` |
| r2 verification JSONL | `581819ffc547cd47d4885c6cecceffa372ce41603c707825bb3f5a529b87267b` |
| query source | `77a685433f4815977207ee32a5ba9cf49d707a993e43a29c169cb12954f0df0b` |
| repaired `.olean` | `8467499d9a4a00bb8afbfcadd9e9dd08866b26c0614a9743d80eda85cef4cb84` |
| repaired `.ilean` | `20becfc8e8705b3446f042e3d85ea580dd5e55192ab8305937944b7934b7c257` |
| complete query stdout | `a54b68f9e54eb717ee2ce2d385cf5138e052c848633da0a8f6cb5f9937aebffb` |

All 62 frozen pins matched on initial and final revalidation. Their canonical
digest, using sorted `path + TAB + hash + LF`, is
`0474c62d41565f73a40a375ab97f73ca2f94a34783acfe751f44a33d0ea4ad91`.
Both r1 P/Q source, handoff, and compiled-output pins match. The r1 receipt
hash is
`daa39582fc9455d444e6acb9daa61665b4bebfb65e53fc168d438b1b46ba273f`;
its failed composition remains failed and is not imported.

All recorded source/input/output hashes and complete stdout/stderr hashes
match current bytes. Invocation order and timestamps are serial. r2 contains
exactly composition then query, both `lake env lean -j1 -M1024`, timeout 120
seconds, exit 0, no timeout. Composition streams and query stderr are empty;
the empty-stream SHA-256 is
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The complete query reports no axioms for raw request unwind, raw failure
unwind, and prefix append; precisely `[propext]` for each initial-prefix
corollary. Printed signatures preserve the frozen premises, length, and all
endpoint conjuncts.

STOPPED. No Lean/compiler/tests, Git, descendants, or filesystem writes were
performed by the reviewer. No active processes or descendants remain.
