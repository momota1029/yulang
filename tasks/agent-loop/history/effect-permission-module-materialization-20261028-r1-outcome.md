# Sprint outcome — EFFECT-PERMISSION-MODULE-MATERIALIZATION/r1

Status: **CLOSED_INCOMPLETE / PIN_MISMATCH**. Contract SHA-256
`4663634216979d18b1378ffcb21e4ae6cc0aca367fb87893e15f0b8175633d24`.
No supplier, source theorem, counterexample or impossibility conclusion.

## Adjudication

The contract recorded a malformed `shadow_apply.rs` SHA-256. It expected
`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a9a78cf72ff`; actual
bytes hash to
`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
The source lane detected this before opening revision-2 authority or source
bytes and stopped. The proof lane independently detected it; its receipt says
it authenticated and opened revision-2 authority plus several other permitted
inputs before the mismatch was detected, while `shadow_apply.rs` body remained
unopened. Its combined read capture truncated, so it made no rule application
or semantic conclusion. This fell short of the contract's authenticate-all-
pins-before-reading condition; treat the proof lane's reads as a recorded
process deviation, not as reviewed authority application. Both workers stopped
and froze only their assigned blocker handoffs.

This is a pin correction problem, not evidence about either pending supplier.
Both remain OPEN. Parent quantifiers, shared witnesses, source domain, semantic
behavior and the separate callback → Call result → tuple component `left`
obligation are unchanged. `AUTHORITY_BLOCKED` is not impossibility.

## Frozen evidence

| Artifact | SHA-256 |
|---|---|
| Fixed r1 contract | `4663634216979d18b1378ffcb21e4ae6cc0aca367fb87893e15f0b8175633d24` |
| Source blocker receipt | `7ad2eafc69ec8385384754fefa1f89372e4aea5d2d7634ca1e3c4a0adebd91c5` |
| Proof blocker receipt | `436cd49389065c95e33a467256c813c18fb19feb81a55f174c395b39559f19f5` |
| `shadow_apply.rs` actual bytes | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| Revision-2 rule source (hash authenticated) | `f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb` |

No compiler, fixture, expected-output or configuration change. No Lean/Lake,
Cargo, tests, build or Git command. No theorem or axiom audit. Preserve the
unresolved `candidate_effect.rs` overlay and `DELTA_AUTH_UNRESOLVED /
NO_SAFE_CODE_SLICE`; old UNKNOWN/quarantined workers and paths remain intact.
Fresh review: NOT_RUN; there is no semantic result to certify.

Next: selector advises whether to issue a versioned corrected contract. Any
redispatch must use fresh output paths; neither r1 handoff may be overwritten
or reused as the corrected audit.
