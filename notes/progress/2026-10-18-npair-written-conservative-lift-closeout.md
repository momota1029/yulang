# Written-field lift sprint closeout (2026-10-18)

Sprint: `npair-written-conservative-lift-20261018`, rev2, contract SHA-256
`704a20cf457ed02ff07b52a399f6440c2fb145d02d6f840db10896f8d892c856`.
Baseline: `f68dc078152bd1a724057a1b12666f517fed5327`; later commits in the
range are contract/state/results only, and source/query pins were independently
checked. The sprint ended with parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR`
OPEN and original conditions **0 -> 0**.

## Proof result

The original Operation image construction supplies the real R response path:
`k0(r,Cnow)=Return(r,Cnow)`, preserving the actual responder `r` and its
existing latent evidence. Authentic `CallMem` preserves its supplied whole
evidence. The retained evidence-fiber calculation forgets to the original
`(d,c,s,pi)` and reflects only when `pi` already exists. It does not create the
fixed original `c` field proof at the actual responder's Written `r.s1`.

The constructive artifact and handoff received an independent CLEAN review.
The independent admission audit also received a bounded CLEAN review after a
one-line receipt correction. Its possible response discriminator remains
UNADMITTED/OPEN; no admitted counterexample was established. W/Z remain
independent alternatives without supplied complete admissions. The first
remaining proof input is the original fixed-c selection/projection rule at
`r.s1`, with its license and full dependency tuple; do not infer it from `r:B`,
root Support, family membership, or Call wrapping.

Artifacts:

- `notes/theory/2026-10-18-npair-written-conservative-lift.md`
  SHA-256 `3482f86bb48869507f0ac89e304d01ad52f378f17456664cf751ad4e97e8e8a6`
- `notes/theory/2026-10-18-npair-written-lift-adversarial.md`
  SHA-256 `c447f90dba0018b139485c9b5cbdc4eeef08e345214d8bf3de245fa9d8b143ed`
- Proof review CLEAN; adversarial review CLEAN in substance; see paired inboxes.

## Implementation result

A fresh compiler review was CLEAN for the exact typed scoped-query bytes and
dependencies. One authorized command ran with 172 seconds left in the lane:

`timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate`

It exited 2 at `solve_scoped_experiment` with
`Collection(ComponentIdentityExhausted)` before returning `CandidateInference`.
No `source_call`, scoped relation/scope, or ordered Replay BoundKey was
produced. No retry or compiler change followed. The example was restored to
SHA-256 `25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca`
and the fixture to `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

Runtime receipt: `notes/progress/2026-10-18-npair-call-scoped-replay-evidence.md`
SHA-256 `25fd000de4f3c9b7bf358b511a29ef28d23171e9b8feae44bfb0f35c53d6492b`.

## Next exact task

Continue the original proof at the missing fixed-c selection/consumer rule and
trace the scoped collection rejection to its exact owner and branch. The next
implementation packet should preserve existing source provenance and
Install/Capture/FreshUse suppliers; do not bypass the scoped experiment through
ordinary `solve()`, delete guards, or treat successful candidate counts as
semantic evidence. Parent quantifiers, source domain, receive route, C1/C2,
F1/FK1, N-Transport, soundness, principality and termination remain unchanged
and open.

Commits/pushes: dependency revision `85ea24bbe`, result checkpoint `0230fb99e`,
receipt correction `73571717e`, compact current-state checkpoint `d9e6949a4`.
