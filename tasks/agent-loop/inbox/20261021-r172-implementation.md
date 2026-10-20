# R172 Luna implementation handoff

Sprint: `source-fact-capture-construction-20261021-r172`, contract rev1
`4d0976759a061241244b06f0eb2ca1c6960f9feb02989eaa73b205e0fd9f108c`.
Luna implementation/query artifacts are frozen and independently CLEAN reviewed
at the exact hashes below. Proof worker `/root/r172_source_capture_proof` is STOPPED on proof
revision 2; its direct-source drain attribution remains UNKNOWN.

Exact current artifacts:

- `crates/yu-solver/src/shadow_apply.rs` SHA-256
  `13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5`
- `tools/inference-playground/examples/r172_source_capture.rs` SHA-256
  `d08852473ae8ce12fd0b8d2d7ee2f5d13e07478609d205de50678fb59ef5c6fa`
- `notes/theory/2026-10-21-r172-source-query.md` SHA-256
  `b1595f946f326573dfd98a580142e02e44b6e7bd11cebc753085707c429e9802`
- Proof note rev2 SHA-256
  `885ca6ca2eba9937cd7bc81ffb6bd384e8fa96d17cc26392b76e7de4a9876488`
- Proof handoff rev2 SHA-256
  `ef35a47437ba1477736f895de4168a8fa8e9f0c43511dd620c9f486891dba1d8`

The query selects exact source provenance, retains ordered dependencies,
replays and candidate Origin rows, and associates the exact relay Apply with
its module callee route, NativeInterface terms and that route's Capture/maps.
It explicitly reports direct-source attribution UNKNOWN, opaque Capture/map
payloads, and no consumer relation join. Its discriminator is therefore false.
The harness uses unchanged R171 fixture ranges and locates A_F in `relay`'s
LocalSource. The conditional Y3 probe is **NOT_RUN**; the query cannot
discriminate the required source-to-consumer association. No build, test,
compiler, evaluator, Y2 or Y3 execution occurred.

No A/B theorem, source/native tuple, solver behavior, or production gate is
closed. R169, R70/R71/R165/R166/Replay, original A/B, F1/FK1 and production
remain OPEN. Only reviewed intended paths may be integrated; preserve unrelated
R152–R163 files.
