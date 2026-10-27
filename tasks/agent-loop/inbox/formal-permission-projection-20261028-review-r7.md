# Independent review: formal permission projection r7

## Recorder provenance

The assigned reviewer `/root/formal_permission_projection_r7_review` had a read-only role and returned this review in its final response. The primary recorded that response at the exact leased path; the reviewer did not write the file. Review execution remained read-only.

## Verdict

**ACCEPT as conditional, incomplete static source evidence.** No BLOCKING, major, or minor finding against r7's qualified claim. **STOP.**

This submission establishes a construction-to-consumer correspondence; it makes no compiler repair and does not merely patch an observed projection symptom.

- The paired constructors at `candidate_effect.rs:1419–1492` preserve Tuple order and implement the required Function equations. Starting from the negative root at `:1659`, Argument flips both variance and selected tree polarity; Result and Element preserve them. The permission constructor at `:1496–1544` therefore selects the original negative live Effect endpoint, including paths through positive intermediate Functions.
- `term.rs:271,831,1166,1230,1253,1292,1358` supports constructor/readback identity under the stated lineage-survival premise. Structural sharing preserves positional traversal.
- `lib.rs:11839,13491` canonicalizes row identities while retaining polarity and structural term keys. Terminating representative lookup at `candidate_intrusion.rs:119` is idempotent. Global forest preservation remains assumed rather than proved.
- Capture's immutable session borrow at `candidate_scheme.rs:1594`, together with the inspected expansion bodies, supports stable canonicalization during capture. At `:1713–1738`, hits retain existing indices; successful misses append a node, pending key, and map association. Expansion at `:1935–2087` preserves those associations. The loop at `:2671–2703` drains pending expansion before successful return.
- Function child kinds and polarities at `candidate_scheme.rs:1973–2027` match the paired constructors. Tuple allocation and offset writes at `:2068–2084` preserve positions despite shared children and subsequent pending expansions.
- Root lookup at `candidate_scheme.rs:2787–2799` and export traversal at `shadow_apply.rs:2650–2686` compose correctly. Final Argument selects field 1; final Result selects field 2. Nonterminal steps select fields 0 and 3. Export retains occurrence, ordered path, source row, and concrete operands separately for each record at `:2688–2694`; coincident endpoint indices create no permission authority.

The reviewer traced double reversal, nested Tuple positions, shared subtree hits, merged rows with distinct polarities, missing roots, invalid final Elements, and allocation-error exits. No successful out-of-image counterexample emerged under the declared premises.

Relevant embedded tests were read at `candidate_effect.rs:2838,3442` and `tools/inference-playground/src/scheme.rs:725`. They support selected sibling cases; they do not replace the conditional argument or establish universal source acceptance.

## Authentication

All nine admitted owner/policy hashes match the r7 contract. Frozen r6 contract, handoff, and review hashes also match exactly:

- r6 contract: `63c7079d33b639e43792a69f543f79eea1c1d9ef5cffce1f6126a4a392c28620`
- r6 handoff: `013821988ef1979b5c530754a8f6c36a440c10ce6c5597fd3e64d1a0cfef749d`
- r6 review: `31eb7c1c774bb7592680c2bc82c9d5d42d2f43d1c3c96cf677ebb9c7e452bd45`
- r7 contract: `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767`
- reviewed r7 submission: `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d`

The corrected receiver locator is `lib.rs:11847`. `candidate_receiver.rs` was neither opened nor searched.

## Remaining obligations

Establish B's transitive construction/parameter/domain/store/export association, reachable-session representative well-formedness, and D's successful capture/export obligations without assuming the endpoint-image conclusion. Then compose this conditional C result with those independently established premises. R1 Lean verification, original parent A/B, source/native correspondence, full inference/executor soundness, and production gates remain OPEN.

No writes, descendants, Git, network, tests, builds, probes, Cargo, or Lean/Lake execution occurred. Baseline Git identity was supplied, not independently resolved.
