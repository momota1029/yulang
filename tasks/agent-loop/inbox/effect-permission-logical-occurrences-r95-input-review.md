# R95 independent exact-input review receipt

Intended receipt path: `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`.
This is Luna's transcription of the read-only reviewer's frozen inline result;
the reviewer made no filesystem writes.

**Verdict: PASS for the exact-input delta review. No execution authorization
issued by the reviewer.**

Start: **2026-10-31 16:53:36 UTC**. Stop: **2026-10-31 16:53:56 UTC**.
Charged elapsed: **20 seconds / 60 seconds**. Effective model/effort: UNKNOWN.

Reviewed the R95 contract, manifest and admission, R94 outcome, unchanged source
dependencies and R93 candidate.

- Contract: 4,210 bytes, SHA-256
  `787d97362f3ca2d7a6a8e742009408513b0ca73a729228ec430db334727e7a1f`.
- Manifest: 5,293 bytes, SHA-256
  `0cc19b0cc76cd5b9a456d62bb3a7d48d656698afefd22c1bc3eccfbd4ed4142c`.
- All 15 manifest input lengths and hashes match.
- Unchanged candidate: 18,460 bytes, SHA-256
  `3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192`.

The reviewer independently reconstructed stdin in memory by concatenating
Syntax, Generation and candidate bytes without separators, removing exactly
Generation's Syntax import and the candidate's Generation import. `import Std`
remains at assembled line 1 and is the sole import.

Result: **106,897 bytes**, SHA-256
**`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`**.
This is exactly 64 hexadecimal characters and matches R95's corrected records.
R94's malformed 62-character digest remains recorded as a historical blocker.

Confirmed ten distinct theorem declarations, each with exactly one adjacent
matching `#check @…` / `#print axioms …` pair at assembled lines 1992–2011:
`inventory_iff_lookup`, `encode_lookup`, `observe_eq_follow`,
`source_membership_iff`, `full_route_unique`, `source_provenance`, `app_exact`,
`lambda_body_exact`, `app_inventory`, `lambda_body_inventory`.

No blocking, major or minor finding in this delta. This receipt establishes
input identity and query coverage only. It establishes no theorem acceptance,
axiom result, semantic admission/readout, standalone-module equivalence or
parent closure. Admission commit `44c1249c8` was supplied by Luna; Git
provenance was not independently inspected.

No Lean/Lake/build/test, scratch/cache, environment creation, Git operation,
source edit or descendant occurred. Reviewer assignment was read-only and
ended after this frozen inline result.
