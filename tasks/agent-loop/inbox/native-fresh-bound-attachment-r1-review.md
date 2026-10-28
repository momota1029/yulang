# Independent review — NATIVE-FRESH-BOUND-ATTACHMENT/r1

Verdict: **REJECT acceptance; close R1 as CLOSED_INCOMPLETE.** Preserve only explicitly provisional, unchecked research. No successful reachable counterexample is established. No execution checks are authorized under Amendment 01.

Reviewer `/root/native_fresh_bound_attachment_review_r1`; requested Sol/medium, observed model/effort UNKNOWN; 600-second grant. ACK preceded body reads. Frozen Rust and Lean outputs were inspected before contract, amendment, handoffs and R5 review/outcome. Read-only; no builds, Cargo/tests, Lean/Lake, checker, formatter, Git, writes, or descendants.

## Findings

1. **BLOCKING — R1 is permanently acceptance-ineligible under its admitted amendment.** The proof producer read the Lean README body during startup, including lines 350–450, before discovering the malformed original pin. Its later statement that construction did not rely on that content does not undo the read. Amendment 01 correctly preserves this as a non-waivable ACK/pin-order deviation and prohibits acceptance, promotion and checks. Close the fixed outcome incomplete; correcting the pin cannot retroactively restore eligibility.

2. **BLOCKING — Lean does not interpret successful native restoration and completed borrowed readback.** `publish` directly inserts the transport, same-bound attachments and admission; `Selected` derives selection from those inserted facts. `beginFresh_current_image` proves only this deliberately successful local projection. No simulation establishes that all successful native branches have that shape, that native HashMap/vector reuse preserves the full key throughout history, or that native closure/completion/readback selects the modeled objects. The last theorem establishes observation OR a changed key, leaving the temporal root-change branch unresolved. Earlier restoration may run Replay and discharge/residual writes before a later bound rereads its parent; no preservation theorem or authentic omitted-image trace is provided.

3. **MAJOR — Rust still does not join each captured bound to actual admission, mapped relation and readback.** Preparation records ordinal, source BoundKey, original parent, effective root and supplied image; `expected_bound_roots` is cloned from those same tuples. Completion selects admissions by `use_origin`, compares relation counts, reads effective roots and compares sets. Antecedent, source-bound identity, mapped relation, child raw key, physical admission, restoration completion and readback are not joined to the original ordinal. Expected `[a,a,b]` and actual `[a,b,b]` pass count and set checks. Swapping preparation tuples checks the copy's equality, not reassociation of native admission causes. Effective roots from `relation_context` also remain conflated with raw retained `relation.key.context`; discharge may change the effective root without losing raw Prefix/weight evidence.

4. **MAJOR — Key/image mutation detection improved, but attachment authentication still rests on preparation copies.** R1 reads key→image pairs and repairs R5's image-set omission. However `map_pairs` and `expected_map_pairs` are both populated from the same `context_remap` iteration. This does not establish that the mapped child's raw native key stores the image. Physical coverage ranges over closure from later effective admission roots, not every preparation-time image. Mutation attempts also skip reassociation/wrong-root when there is at most one bound; swapping tuple positions does not require authentic duplicate-bound occurrences.

5. **MAJOR — Required authentic module/local cases remain absent or insufficiently asserted.** Display/where selects routes with shared children and weights but does not establish discharged-parent temporal restoration. The identity-named module specimen does not assert that the context is logical identity with no allocated identity row. No dedicated successful-empty specimen is asserted. A pause writes Partial and returns `context_completion`, but no assertion consumes that field to establish the pre-bound frontier and continuation. Explicit identity, successful-empty, real pre-bound pause, shared-child/selected-weight, and discharged-parent restoration evidence is still required.

## Useful bounded repairs and unchanged scope

The test-only Rust diff now excludes logical identity from required physical rows, consistent with native allocated IDs starting at 1. Pair tracking makes image replacement and a two-image swap affect the predicate. The Lean list interner derives reuse/append raw-key facts rather than assuming a lookup law, and distinguishes raw contexts from effective discharge/residual reads and mapped from admitted relations. These local constructions remain **NOT_CHECKED** and lack native interpretation/completion.

The original parent remains `∀ s x d a, supported s → generates s x d → solves d a → ∃ e, sourceJudgment s x e ∧ sameScoped s x e a`. No source instance/shared witness is constructed. Original supported-source, lawful-history, retained-occurrence, A/B, principality, termination, executor, effect and production gates remain OPEN. The selected effect policy is unchanged. Full abnormal-path restoration is not added as a general correctness requirement.

## Hashes and execution

| Artifact | SHA-256 |
|---|---|
| Base contract | `fd040b8a5a1702b54c06c44fa88a8316433dc950a62d453de48db3f73e2e6e2c` |
| Amendment 01 | `51f0867e885940a163a5f9c31bd751593911830da9edfefb54788c321f17f0d1` |
| Rust source | `894e0b9d158bbcf5a7f7184eca740762ee03623e07d83bcf250fdc46bcb9edb5` |
| Lean source | `9327161449d8f286b15af23394033b35615b8530363587ca79d22f5d1a40be9f` |
| Rust handoff | `43a54b18f27afa664ac3cffc58889667c58650aeba3d41c2796232fa36a99183` |
| Proof handoff | `99c0f7f077c3d8838cc5bdeeff4ead15cad53cec782857332bdcae94a7740314` |

All admitted Rust owners/manifests, Lean inputs/configuration, authority/correction/progress pins, R5 contract/outcome/review and R5 handoffs matched. The README matches only the corrected amendment pin `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`; the original was malformed at 63 hex characters.

All eleven authored Lean terms are **UNCHECKED**. Kernel acceptance, printed theorem types and complete axiom audits are **NOT_RUN**. Exact elapsed/CPU/RSS UNKNOWN. The reviewer ran no execution checks and stopped after one read-only verdict.
