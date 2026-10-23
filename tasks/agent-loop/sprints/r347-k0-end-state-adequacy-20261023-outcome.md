# R347 outcome — K0 generated constraints and actual end-state adequacy

Disposition: **OPEN; correspondence not established.** This closes the R347
assignment and does not close R339-D2, R345-N, full N, or the original A/B
obligations.

## Frozen target and evidence

R347 revision 2 fixed the target at the authentic ordinary K0 source domain:
for each completed native state `S`, compare the satisfying assignments of
R341's actual-state formula `H₀(S)` with the occurrence-indexed source
constraints `C_s`, under an exact kind-preserving row map and projection. The
reviewed R341 direction `H₀(S) ⇒ C_s` remains available only under its stated
premises. R347's new obligation was to extend every `σ ⊨ C_s` to actual native
coordinates satisfying `H₀(S)`, or freeze the first exact obstruction.

Frozen inputs:

| Artifact | SHA-256 |
|---|---|
| R347 revision-2 contract | `3ff5884ffefb9dca31f5433b68af56f3c6f172feab2284c1c80235dbfbe7ac5b` |
| R347 revision-2 source census | `f40856702e43bcf4b990e980bee841292b792c372c7ba99dea1c6ea10b87eb7f` |
| Lambda row census supplement | `157edb3eb6588d3b18e53d9376b5e4a4c9a522d27d9d63bf3a215b374949d3d6` |
| governing whole-language semantics | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

The supplemental source trace records that ordinary Value-Lambda admission
allocates Lambda entry and returned Effect rows, and ordinary Apply admission
retains its invocation Effect row. These are actual `D_s = FV(C_s)` coordinates,
not disposable complement rows; arbitrary source assignments on them must be
preserved. The supplement also pins the `ConstraintBatch::emit` and source-fact
append path. It is an owner census, not the missing extension proof.

## Assignment and resource receipt

The proof assignment was `/root/r347_k0_end_state_prover`, requested
`gpt-6.1-sol/high`; effective model and effort were not independently observed.
The worker byte-verified the frozen R347 revision-2 contract, census,
supplement, and TeX, then stopped writing at **2026-10-23 10:15:01 UTC**.
The original assignment's exact launch time and fixed expiry are **UNKNOWN**.
The worker explicitly did not resume, did not issue an active-work receipt, and
created no proof, handoff, or scratch artifact. Therefore the proof and handoff
are **ABSENT**, and independent review is **NOT RUN**. The stop receipt is
recorded in `current.json`; the stopped identity's old proof leases are released
only as part of this closeout and confer no R348 write authority.

Charge the full 3,000-second proof grant conservatively; do not infer actual
active time or return unused time. R347's primary source allocation was
2,400 seconds. The 1,500-second reviewer was never assigned and is discarded.
Primary closeout/integration is capped at its existing 300-second allocation;
there is no carryover or reset. No tests, builds, probes, source changes, or
compiler edits were made. The implementation disposition remains
`NO_SAFE_CODE_SLICE`.

## Candidate route is not a proof

The stopped worker sent a message sketching a possible support-preserving lift:
replay successful prefixes over `D_s`, preserve every non-bottom source
coordinate, and put genuine unused complements at bottom/empty. The message did
not freeze a derivation and is not admitted as evidence. It does not resolve
whether every final auxiliary row can be assigned while satisfying all
completion, replay, and frame formulas. In particular, it may not assign
Lambda entry/return Effects or Apply invocation Effect to bottom merely because
they are auxiliary in the native state.

No concrete separating valuation or authentic compiler counterexample was
established. The result is an **unfinished proof**, not a falsification, a
coverage finding, or a compiler defect.

## Exact remaining obligation

For every `σ ⊨ C_s`, construct a kind-preserving extension `ρ` to every actual
native coordinate with exact `restrict_source(ρ) = σ`, and prove `ρ ⊨ H₀(S)` for
each authentic completed `S` in scope. The argument must account for:

1. all source origins and actual admission/suppression owners;
2. Value-Lambda entry/returned Effect rows and Apply invocation Effect rows;
3. every other final auxiliary coordinate and its row map;
4. each native formula's derivation through propagation, replay, ownership,
   intrusion/finalization, and successful completion; and
5. the exact projection and its converse, composed with R341 only under R341's
   unchanged premises.

The next packet is R348, a new, separately budgeted assignment to this same
bounded theorem and source domain. It rederives its own proof route, reuses the
frozen evidence only under each artifact's stated scope, and keeps the original
Simple-sub A/B quantifiers unchanged. The newest TeX governs whole-language
semantics; this K0 relation is not its evidence-hole field `H`, its world-indexed
value/computation relation, complete-Call evidence, or `Y_H`. Q1–Q8,
`BuildLocal`, finite-certificate search/completeness, principality, full N, and
production remain OPEN.
