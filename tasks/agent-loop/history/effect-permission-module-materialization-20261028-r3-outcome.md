# Sprint outcome — EFFECT-PERMISSION-MODULE-MATERIALIZATION/r3

Status: **CLOSED_INCOMPLETE / GOVERNING_READ_TRUNCATED**. Contract SHA-256
`7b608b5640caf26f076c8e5e9befeb297c5a9552f913bbb4d074a3025406b727`.
Neither supplier was semantically audited; no parent conclusion follows.

## Authentication and stop disposition

Primary froze a 21-input manifest and preflight script, authenticated the
bootstrap files, and ran the exact command successfully. Both independent lanes
then repeated the exact bootstrap and all 21 manifest hashes, with the marker
`PREFLIGHT_21_ENTRIES_ALL_MATCH` and exit 0. Afterward, each lane's batched
governing/contract read produced aggregate output truncation. The governing
output itself contained a truncation marker. The r3 contract required immediate
STOP on any truncation, with no excerpts, smaller retry, fallback or further
body inspection; both lanes stopped and wrote only their leased receipts.

The successful preflights establish byte identity of the listed inputs only.
Because neither lane completed its admitted reads, neither produced a source
audit, applicability result, theorem, axiom audit or supplier disposition.
Truncation is a tooling/transport blocker, not a semantic counterexample.

## Frozen evidence

| Artifact | SHA-256 |
|---|---|
| R3 contract | `7b608b5640caf26f076c8e5e9befeb297c5a9552f913bbb4d074a3025406b727` |
| R3 manifest | `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11` |
| R3 preflight script | `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133` |
| Primary preflight receipt | `d0338bc3080e18652762f0815aa73186f187afd7448aeba36c47335eabf011ee` |
| Source STOP receipt | `76e2b6edb486485cc8bfac35e0780e15a103d1768f09d9ba9e6f71b9db8c5d25` |
| Proof STOP receipt | `3c90dd78b24bc699c6abd088ff302feb6147de8e7ebac9c7337bc72a3a584721` |

Both 200-second lane reservations are fully charged; no refund or reuse is
claimed. The full r1/r2 charge of 1400 seconds remains. There was no Lean/Lake,
Cargo, test, build, Git operation, theorem construction, optional Lean file,
or descendant dispatch. The fresh independent review was not run because both
producer lanes stopped before producing semantic findings. Their final roster
states are terminal; their receipts are frozen.

Preserve both module Call suppliers and the original parent quantifiers,
shared witnesses, and separate callback → Call result → tuple `left` obligation
as OPEN. Keep all earlier UNKNOWN identities and quarantines intact, and retain
`DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE`. No source or expected-output files
were changed by this sprint.

Next disposition: await the sprint selector's bounded recommendation for a
successor that avoids aggregate output truncation while preserving complete
authentication and fail-closed reads. Any successor must use fresh paths and
grants and leave all prior artifacts unchanged.
