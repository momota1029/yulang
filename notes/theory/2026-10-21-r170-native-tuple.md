# R170 retained Capture observation

Status: frozen provisional implementation/source/probe evidence, result revision 3 (supersedes revision 2, SHA-256 `412337428fcc956523e46c970cb3800aa77c88a0dd0fb6758a77ce6f66ba2984`). Independent code review and source-domain review are CLEAN for the scoped §1 ignored-input case; a separate review confirms this fixture does not supply §6's direct-Name witnesses.

## Scope and pins

This is a borrowed diagnostic view over data already retained by the candidate solver. It adds no solver state, admission, propagation, rollback, or inference behavior. It does not certify a source fact, unique provider event, or parent theorem.

- Contract: R170 revision 6, SHA-256 `f099fe9e5d10420413a20ffae5916a7961767e5ed76f592240c19d89e643f74b`.
- Baseline: `5837ec19220cc6f0c7e0d8f106dee59e3bbad9a`.
- `candidate_scheme.rs`: `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225`.
- `shadow_apply.rs`: `46959cf65e447f4c1dc3db34f1969cfa5746e8d7b86227b1b8b456ac2701ddbb`.
- Example `r170_provider_incidence.rs`: `d6392dde7fc2aedd4e5c860e75f89df0217bb621598558bf99817d9cc1d5d3a4`.
- Probe receipts: stdout `966303fac00a6f369eeb5ee92f0049e41f7b26dc3ab2e79994fb5d1c651188bc`; stderr `53fe0c22ed791aed2a6ec369e5fe32ca70b762d433537b2c764e6586859e956a`; status `68c10920ac9b4b082ad35849d64232dd27adbe99c2c22f108f9104548d052cad`.
- Read-only fixture `entry-computation-argument.yu`: `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`.

## Borrowed records

`CandidateInference::ordinary_provider_observation` retains its relation-local FunctionPort/dependency/admission/emission/Origin rows and now also exposes module and Local capture routes. Capture rows identify graph index, route owner/index, the authentic route occurrence, retained `context_use`, optional bound relation, and ordinal. They borrow each existing capture graph, its individual captured Bounds, each linked EvidenceSnapshot, and the actual route-owned fresh-use maps (`scope_remap`, scoped relations, Terms, effect operands, bundle remap, context remap, evidence remap).

Provider and capture rows share one 256-row hard limit; the example requests 48 total. `truncated` remains explicit. The example also caps each rendered record at 360 characters and labels truncation. A bound relation matching provider `q` is only a relation-local overlap candidate: the API and example explicitly do not infer provider-to-Capture incidence from equal relation IDs. `lambda_slot2_source_join()` remains `NotJoinedToContextRecord`.

## Source-domain limit

The pinned fixture is an explicit Computation formal with an ignored `int` input and ground-returning `signal::ping` invocation. It has no source FormalName `x`, so it cannot establish the original §6 direct-Name witness bridge. Any probe can at most supply an ordinary AE/RE provider Capture-incidence example for this ignored-input source case. The CLEAN-reviewed proof lane records the source-domain derivation and exact missing source-fact/provider-map/consumer association separately.

## Review and probe outcome

The fresh independent code review was CLEAN for the exact code/example hashes and borrowed-only boundary. A fresh source/native review confirmed the fixture belongs to the parent's §1 ignored-input/ground-return case: §1 permits ordinary calls, operations and unused latent inputs, and imposes the FormalName condition on forwarding edges. This fixture has zero forwarding edges. It is outside §6's direct formal-Name subcase because `ignore(signal::ping())` passes an operation expression and the body returns `9`; therefore it cannot supply §6's direct-Name mapped-admission witnesses. This does not exclude it from the narrower §1 diagnostic case.

The single authorized in-repository candidate probe completed with `probe_status=0`; `process_group_status=0` and `process_scan_status=0`. `cargo run --offline --locked` built and ran the example in about 20 seconds. It observed provider FunctionPort parent relations `q=36` and `q=54`; the one retained module Capture route had `context_use=1` and captured-bound relations `q=14,3,4,11`. Row selection is complete under its 48-row request (`truncated=false`); individual rendered record strings may still be truncated at the example's 360-character display cap. These different relation IDs do not prove a source-qualified mismatch: the probe did not authenticate a source FactId/Terms to the same provider route/maps and consumer q, nor enumerate a justified shared-anchor/transport/Replay join. No source-fact/provider-Capture incidence or §6 direct-Name admission is claimed.

No tests or Yulang2 execution occurred. The one Y3 candidate probe ran in this repository under the reviewed network/filesystem/process bounds. R169-SOURCE-FACT-CAPTURE-INCIDENCE-1 remains OPEN, as do R70/R71/R165/R166/Replay residual, original A/B and production gates.

Historical correction: the revision-2 draft ended with a stale `NOT_RUN` paragraph written before the authorized probe. This revision supersedes that paragraph with the execution receipt above. No second probe or test was run for this correction.
