# Frozen source handoff — EFFECT-PERMISSION-MEMBER-OWNER-REPAIR/R99

Assignment-ID / revision: `effect-permission-member-owner-repair` / 1.
Parent task: Luna-admitted R99 packet, pushed base `f3ec6f1dd`.
Exact writable paths: `crates/yu-solver/src/candidate_receiver.rs` and this handoff only.
Baseline / direct source hash: `candidate_receiver.rs` baseline SHA-256 `03553455bb3b0a4cb0f0ad2fb04b1b8dbf8fac00982547323fe8b6439edbb34d`.
Outcome class: owner-local compile repair.

## Result

At the formal-registration ownership validation, replaced the exhaustive `SourceRootId` variant match with `local_source.hir.owns_source_root(&registration.owner)`. This is the exact ownership predicate requested for the source-root domain and avoids duplicating the enum's variants in this owner. Existing `Definition`-restricted checks elsewhere in this file are predicates specific to operation/module owner cases; no other exhaustive `SourceRootId` match requiring a repair was found in the leased file. No other owner or semantics change was needed.

## Verification and limits

Static search of `candidate_receiver.rs` found no other exhaustive `SourceRootId` match. No Cargo/build/test, Git command, scratch, generated output, or environment change was performed. No independent review or compilation evidence is claimed.

Final `candidate_receiver.rs` SHA-256: `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.

The original parent/source/native theorem and production gates remain OPEN. No descendants or disposable scratch were created. All writes ceased before handoff hashing: **STOPPED**.
