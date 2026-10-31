# R87 outcome — finite drain-reader correspondence

Status: **PASS / CLOSED_BOUNDED_RESULT**  
Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`  
Baseline: `9931800b1aed04402049a0e7685630f24b9e5e56`  
Authorization for final call: pushed commit `80ff09f9b`.

## Final result

The separately reviewed slot-2 Lean stdin completed with exit **0**, no timeout, in **13.610 seconds**; peak child RSS was **947,296 KiB**. The exact 151,068-byte stdin hash is `f41122e303840b53eb364a76542f263a2554f6174fa9e14187e1f2b912e6812a`. Lean executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

Complete stdout: 138,435 bytes, SHA-256 `56ab6f6bc6aa551371736d65ea1e352b7bf21b8aab01a6437f7996639a62d329`. Stderr is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Raw receipt: `tasks/agent-loop/history/native-drain-reader-correspondence-20261031-r87-slot2-raw-result.json`, SHA-256 `6e3fc7381194fd275bfede007a9dffae64d39008934a7adc20f3665ee5f71728`. The flattened stdin and temporary Lean source were never written to disk.

A different reviewer from the proof author independently reconstructed the full input and audited the complete output. Exactly **13 R84 + 11 R85 + 35 R87** theorem type/axiom pairs occur once each, with no missing or duplicate names. All 59 printed types match the previous slot's types. There are **zero errors**, **zero `sorryAx`**, no project axioms, `Classical.choice`, native-evaluation shortcut, or checker bypass.

R87 axiom profile:

- **No axioms:** `clone_pending_distinct`, `clone_fields`, `uncut_guards_ignore_completed_bit`, `cut_receipt_pending`, `internal_receipt_completed`, `cut_and_internal_cannot_share_attachment`.
- **`propext` only:** 23 declarations.
- **`propext, Quot.sound`:** `publicationData_iff`, `uncut_sound_complete`, `cuts_sound_complete`, `checkedCandidates_ok_iff`, `internal_sound_complete`, `saved_sound_complete`.

The 37 warnings are four deprecated conditional-lemma warnings, 31 unused section-variable warnings, and two unused simp-argument warnings. None is an error-recovery diagnostic. The independent audit verdict is PASS; its reviewed receipt is recorded at `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-slot2-review.md` (pre-execution) and the result-audit verdict was returned by `/root/r86_repair_review`.

## Scope closed and remaining

R87 closes the finite relational correspondence for the distinct uncut publication, cut-window, Internal and saved receipt-factor readers, including their stated soundness/completeness, branch rejection and uniqueness properties. It also supports only the explicitly conditional R57/R84 obstruction stated in the candidate. No reader's success is substituted for another's.

Still OPEN: native extraction and whole-crate transition coverage; pointer-token and shared-payload authentication; the same-snapshot `Saved.otherChecks` equivalence; selector/projection bridges including R57 relation-ID versus R84 occurrence/route uniqueness; standalone module imports; the original Simple-sub A/B theorem at R66 `Root`; and production. The source proposal remains a proposal and no Rust/compiler semantics changed.

Slot 1 remains recorded as failed with four proof-normalization errors and `sorryAx` recovery; it is not overwritten. Slot 2 was the final call. Total calls used: **2/2**. Proof/source lanes are STOPPED; no third invocation is authorized. No tests, builds, Lake, Rust compiler, or standalone-import check were run under this sprint's exclusions.
