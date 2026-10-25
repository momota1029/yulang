# R51 process evidence review and Luna adjudication

R51 disposition: process evidence accepted after bounded minor-finding adjudication. No new mathematical acceptance is claimed. R50's semantic review is reused only for its original bounded empty-owner claim.

## Independent review

Fresh compiler_referee review verified the R51 contract/manifest/verification/R50-review hashes; all 11 dependency pins; candidate and audit byte hashes; resolved native Lake path and binary hash; all eight raw output hashes; successful exits for all four calls; the exact one-import root delta; and compliance with the 4-call, 60-checker-second and 420-active-second limits. No BLOCKING or MAJOR finding. The reviewer used zero Lean/Lake/checker/build/test/Git/network/write calls and made no descendants. The full <=180-second reviewer grant is conservatively charged.

## Minor timing finding and Luna adjudication

The reviewer independently observed two clock discrepancies. For call03, UTC start/end span **36.288799 s** while monotonic duration is **35.166319924 s**, difference **1.122479076 s**. For the packet, UTC span is **75.121829 s** while monotonic active duration is **72.873617432 s**, difference **2.248211568 s**. The cause of both is **UNKNOWN**. Original timestamps, raw captures, manifest and verification receipt are preserved byte-for-byte. Both wall and monotonic values are below their caps; budget accounting uses the recorded monotonic durations.

Luna accepts these two findings as **MINOR** under R51 contract revision 2 because the complete native executable provenance, raw captures, pinned dependency chain and monotonic budget evidence are independently verified. This adjudication does not waive missing or over-cap evidence generally. R50's separate 1.072710997 s clock discrepancy remains unresolved and unchanged. No rerun was authorized or performed.

## Frozen pins and outcome

- R51 r1 contract SHA-256: `7c79cc4cb903a9df69ee7b8cbacbb1136c33c46242cee084ebdae708072ddd34`.
- R51 r2 contract SHA-256: `bc814b87f9c746dd7a72a193499f0791f7ad6630cf4a64ee3fe96357dbb6c400`.
- R51 manifest SHA-256: `4831a32b64fe81fd2cb3935f79003134ee83a30be05f29fc0e76400d62024344`.
- R51 verification receipt SHA-256: `13a4dbe27c7da65949be229c3db9d3f99c3445599e81ef1f741134486812e9cd`.
- R51 Lake resolution record SHA-256: `0b7896a98c3d3356bf930ffbf5986325fdca5aed356d6815c730280dc01e2f3b`.
- R50 semantic review SHA-256: `a1438c78a0cc2a6d5105fd07687f6b73902c0893f2257f13855b4fe2a139eaa3`.
- Candidate SHA-256: `5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935`; audit SHA-256: `7cc577fff482bac2674c6449b43cf89edfb04c9bc258c6bfaf3e5bed499aea3e`.
- Primary: 4/4 calls, 37.933119739 checker seconds, 72.873617432 monotonic active seconds. Reviewer: conservatively charge 180 seconds. New R51 grant: 600 active seconds, 4 calls, 60 checker seconds. R50 grant remains fully charged and unchanged.

Adjudicated next action: integrate only the byte-identical candidate and one-line root import; run the required static consistency check; then record R51 integration. Preserve R50 as RESULT/EVIDENCE_INCOMPLETE, all parent gates OPEN, withdrawn questions withdrawn, and eight legacy reservations quarantined.
