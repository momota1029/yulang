# R43 integrity correction: final theory-note hash

Date: 2026-10-19
Sprint: `original-output-order-20261018-r43`
Scope: metadata correction only; no semantic or theorem change

The R43 theory note's frozen handoff and `current.json` recorded SHA-256
`d6fb7eab0f388044aefcfdcc6276da11875d56153c438792d87e652eca5675c9`.
Before the R43 commit, Luna removed trailing Markdown hard-break spaces so the
exact staged diff would pass `git diff --cached --check`. This changed the
file's byte hash without changing its words or meaning. The committed note's
actual SHA-256 is
`50c8499da6b441980953868e007fc8f22446a8cea19d1015d7ad8affedeb5c61`.

The note at that hash is the authoritative final R43 artifact. The original
handoff is preserved unchanged as provenance; this receipt supersedes only its
stale theory-note digest. The R43 contract remains
`065f0983dea404bb278810ca4b82d430049bfbcb0ce6413236fc05e407a16387`, and the
handoff remains
`09d721a138c8a9aa6e4aa9017e489fd75bdfe051f7a10876fb8e08f15ebafa51`.
The bounded conclusion, parent status (**OPEN, 0 → 0**), and stopping condition
are unchanged.

Luna found and corrected this metadata discrepancy during the 2026-10-19
resume audit. The source bytes were rehashed directly; no test or compiler run
was used. No unknown-owner path was read or changed by this correction.
