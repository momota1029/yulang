# R265 — derive module-local syntax environments for the pinned Y2 sources

Status: ACTIVE primary-only diagnostic investigation.
Branch / baseline: `research/simple-sub-intrusion` / `944b7fc1e`.
Authority: unchanged Types/Console goal; R149 and R261-R264. This packet
continues source evidence only and changes no language semantics.

## Outcome

R264 showed that empty and all-source syntax environments are both poor
controls. Derive, for each exact pinned standard-library source, the imported
operator headers indicated by that file's own scanned imports, then check
whether a comment-only input projection parses without structural recovery.
This remains a Y3-parser diagnostic control; it is not presumed to implement
Y2 re-export or ModuleMap semantics.

Success evidence: authenticate all 40 source blob IDs; report import-module
resolution and environment-construction failures by source; parse every
comment-projected source under only its derived direct dependency headers;
summarize syntax diagnostics, structural recoveries and root kinds. Stop if
the current header scanner cannot account for a module's source imports, or
if imported operators conflict. Do not substitute all-source headers silently.

## Scope and resources

Read the embedded standard-library bundle, `pinned_stdlib` module mapping,
`yu_syntax` header/environment APIs and relevant R149/R261-R264 records. A
temporary primary-only test may exercise the control and must be removed.
No retained source/test changes, builds beyond the focused Cargo test, sample
execution, external reads, or parser semantics. Cap 420 seconds, no carryover.
No independent reviewer is assigned; any result remains provisional.

R149 source/root identity, accepted Types, Request reachability, outputs,
Simple-sub/evaluator A/B, R70/R71, source/native proofs, soundness,
principality and production remain OPEN. A successful Y3 parse still needs a
Y2 syntax and registration correspondence proof before runtime use.
