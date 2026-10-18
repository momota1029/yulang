# R44 independent review and adjudication

Status: candidate rejected for adoption; no implementation authority
Sprint: `call-output-owner-jof-20261019-r44`, contract SHA-256
`8a9cdf31c8ce33feb30673a7cb91c099173ecd1da44e37e76b27d951960a91d8`
Reviewers: fresh `/root/r44_compiler_referee` and `/root/r44_spec_auditor`
Parent: unchanged inference/evaluator theorem and Simple-sub A/B, **OPEN, 0 → 0**

## Frozen material reviewed

- JOF draft: `notes/design/2026-10-19-call-output-owner-jof-r44-draft.md`,
  SHA-256 `af9765c72edb19ef7c888e0c6751518ba3a1ccf79c5c99d7297796c1346d84fb`.
- Formation attempt: `notes/theory/2026-10-19-jof-application-formation-r44.md`,
  SHA-256 `a06c546be1204eb16bf81f3c45a3aca6f05db148cc00ea9e3f2fd971e62b0c12`.
- Evaluator corollary rev2:
  `notes/theory/2026-10-19-jof-application-evaluator-corollary-r44-rev2.md`,
  SHA-256 `bb7aff3ed064b7118861f8da67df2d69bd0392c783df7e4864d1a811b112d3ee`.
- Primary scope audit:
  `notes/progress/2026-10-19-r44-jof-scope-dependency-audit.md`,
  SHA-256 `172eb876bb50d8439a996cb411af537eb3f526e4dfc951c5fb996b666eb0e9cc`.
- Implementation boundary:
  `notes/progress/2026-10-19-jof-implementation-boundary-r44.md`,
  SHA-256 `5478d92e69688b26b0b2e6e0564df1efa5d06ef98aeaed5dd222110be4603a21`.
- Handoff: `tasks/agent-loop/inbox/20261019-call-output-owner-jof-r44.md`,
  SHA-256 `8f152527fd7a6432c7dde63bf91d5dfe8093d042488d185b3f0c4c751cb8d575`.

## Adjudicated findings

Both independent reviewers confirm the candidate does **not** meet R44's fixed
success evidence. Their reports independently identify these blockers:

1. **The output dependency telescope is unconstructed.** Draft §4 and formation
   proof §3 equate `Delta_A` with available context `Gamma_q`. The authoritative
   Generalize definition (§3.3) requires the declaration's exact free-dependency
   telescope, separately from its type scope. Identity inclusion proves
   availability but not dependency ownership. The candidate's
   `Delta_A := Gamma_q` claim therefore remains unjustified. No replacement
   `D_q` is established by this review.
2. **The required q instance is incomplete.** The proof attempt leaves the
   authentic Application/effect origin, complete ordered Call headers and arms,
   and explicit copy/frame mappings open. In particular, it supplies no
   two-independent-frame and alias Generalize certificate. Source-interface
   construction consumes authentic source premises and cannot create those
   missing owners. R44's specified outcome is unmet.
3. **The evaluator corollary is properly conditional.** Rev2 accurately
   requires independent Code-Call, result-port, compatibility-origin and full
   suffix premises. It proves no q typing, source-fiber preservation or parent
   theorem closure.
4. **A provenance pin was mistyped.** The actual SHA-256 of
   `notes/theory/2026-10-07-call-input-construction-proof.md` is
   `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6`.
   The R44 contract and evaluator-corollary rev2 omit `874` in the pin. This is
   a transcription defect; this receipt and the mutable current snapshot use
   the verified digest. Frozen originals remain unchanged.

The compiler referee additionally gives a strategy-level risk example: an
unrelated preceding challenge could become an output-strategy argument and
allow challenge-dependent `Int`/`Bool` choices. This demonstrates why
availability is not enough; it is not asserted as an observed acceptance
change in the target program. It also notes that a W arm returning another
provider needs that provider's own admission/future contract, and that an
alias must preserve its shared frame rather than receive a fresh independent
choice. These are concrete obligations for any future construction.

## Decision and next boundary

R44 is closed as an unsuccessful design candidate at the identified boundary.
JOF remains non-Authoritative. No compiler code, test, expected output, build,
Cargo command or runtime execution is authorized or changed. The original
parent remains OPEN, 0 → 0. Continue only after selecting a new bounded sprint
that attacks the missing authentic output owner and retains independent review.

Reviewers performed read-only source inspection and hashing. Neither edited
files nor ran tests, builds, Git or runtime commands. Luna adjudicates these
reports; the reviewers do not promote the candidate.
