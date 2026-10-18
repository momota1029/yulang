# R37 native Apply/copy bridge candidate

## Outcome and parent application

This is a test-only native candidate for `authentic-apply-copy-bridge-20261018-r37` (revision 1, contract SHA-256 `acc03f679b76a8b7b64492b1174a492907c4014cb23e2ead6e888be006baaa4a`). The original theorem remains `0 -> 0`; no source scope, proof premise, semantic rule, or production gate is closed.

The exact nested `q = loop y` Apply is now joined through four separate records:

1. Its checking occurrence selects the triggering typed comparison and source event. Both C/D extrusion records retain that same full structural `TypedPairKey`.
2. Each generated signed link retains its own `Parent.copy`, `Parent.parent`, and polarity. The test checks the argument coordinate/polarity and result coordinate/polarity independently.
3. The helper capture is looked up by the intrusion map's canonical representative. The recorded capture request may be another alias: it is authenticated by canonicalizing that request to the recorded representative. The signed request, representative, and graph row remain separately visible.
4. Each of the two selected helper `FreshUse` routes is checked through its own row and reconstruction maps, for both signed coordinates. Each route image is validated from its owning reconstruction observation. Fresh images differ from the source representative; shared or reused images retain it; a canonical-map hit retains its existing image and earlier first-entry row.

The fixture distinguishes the direct `loop x` Apply from nested `loop y`, counts three literal helper Name uses, and selects two actual helper routes. Negative controls cover wrong Apply occurrence, wrong trigger comparison, wrong C/D coordinate, unrelated source event, sibling route, and mismatched reconstruction map. The third literal helper use is not treated as one of the two selected routes.

These assertions remain unexecuted pending both clean independent native reviews and Luna's separate launch receipt. Even a later green test would establish only this exact native trace, not the source `TypedPortRef(R)`, C/D copy scopes, typed publication, or the original parent theorem.

## Source, propagation, and consumer correspondence

The inspected owner path is `local_source` nested Apply -> `candidate_source::emit_candidate_source` scheduled recipe/checking occurrence -> `candidate_call::ApplySourceInput` -> `shadow_apply::admit_candidate_fact` -> `candidate_extrusion` generated `Parent` records -> `candidate_intrusion` active group/source association -> `candidate_scheme` installed helper capture and each retained local `FreshUse` map. The repair adds assertions in the existing test module and an integration regression; no production prefix or solver behavior is changed.

The independent R37 falsifier confirmed that `Capture::row` canonicalizes before storing a capture record and returns early on an already present canonical row. The join therefore does not require the raw signed request to appear literally in `capture_rows`; it authenticates the canonical representative through the recorded owner map. This is a source-code guard only. No claim is made that the exact fixture exercises an alias collision or a canonical-map hit until execution supplies that evidence.

## Historical expectations and prior evidence

The approved R36 native target and closeout were read before edits. Luna also preserved its exact candidate patch as `notes/progress/2026-10-18-r36-native-candidate.patch` (SHA-256 `5eeaebc5b25826e75793ce43136f4af79458346005ab7d695eeacfdb9b74058e`), which I checked against the working delta. Its findings were retained: the former join conflated the triggering comparison with the generated copy link and conflated a signed row with a route image; the R36 test also had a missing delimiter. The current test-only target diff does not touch snapshots, goldens, diagnostics, or other expected-output files. Existing integration assertions are preserved; the source regression is additive. The integration test file remains byte-identical to the R36 candidate (`47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`).

Reused the R36 exact nested source fixture, source Apply/checking anchor, helper route ownership, and bounded negative-control plan. Rejected the earlier existential endpoint join and any requirement that sibling routes produce unequal images. The R37 falsifier's canonical-row observation was incorporated as a permissive canonical-map lookup, not as a claim of fixture incidence. No withdrawn Simple-sub bypass was restored.

## Exact boundary and next owner

- Native implementation/review gate: OPEN until the frozen target receives clean compiler and spec reviews.
- Execution gate: OPEN. No Cargo, build, test, or probe ran. The exact focused Cargo invocation remains gated on clean reviews and Luna's explicit launch receipt.
- Source correspondence: OPEN. The native records do not derive the actual `TypedPortRef(R)`, `CopyScope(C/D)`, or typed publication action from adopted source owners.
- Parent theorem: unchanged `0 -> 0`; F1/FK1, N-Transport, complete Call/effects, soundness, principality, and termination remain open.

Mutual TODO `R37-SOURCE-TYPED-PORT-COPY-PUBLICATION` asks the source Apply/Call/Generalize owners for the exact original result telescope, C/D copy scopes and dependency inclusions, and typed publication action at this occurrence. The first absent owner field is the falsifier; a constructed auxiliary that assumes those fields is not closure. The corresponding later native TODO is to execute the exact join and report any missing side/pair/group/canonical capture/route-map edge without changing expected output.

## Frozen evidence and resources

Contract and direct source/native dependencies were rechecked: `local_source.rs` `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`; `candidate_source.rs` `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`; `candidate_call.rs` `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`; `shadow_apply.rs` `5bbcf27d51906814ba38b2b9b10ff58369da540` is the handoff's truncated pin, while the rechecked full-file hash is `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`; `candidate_extrusion.rs` `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`; and `candidate_intrusion.rs` `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`. The test-only production-prefix byte count/hash remains the R36 pin: 119639 bytes, `bc809becb6dc89149e2d00057f1d65b879121668f5485fef9d6a493d64f08a18`.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. Assignment grant: 1200 seconds. Runtime duration metadata is unavailable, so conservatively charge the full 1200 seconds; no tests or probes consumed. No new scratch paths or descendants. Existing quarantined paths remain untouched, including `tools/__pycache__/` and the R37 current-state quarantine note's replay-constructor artifacts.
