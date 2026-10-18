# R47 independent compiler review

Reviewer: `/root/r46_compiler_review` (fresh R47 assignment)  
Requested role: `compiler_referee`; observed model/effort: **UNKNOWN/UNKNOWN**.  
Review result: **no BLOCKING, major or minor findings** within the bounded
obstruction claims.

## Frozen target

| Artifact | SHA-256 |
| --- | --- |
| R47 contract | `aba8009c8ec658af48ed2844e6a9c9b4554b4343ada19f8a7aae85b978574131` |
| Proof artifact | `2a8a076a2d245baf367a377a167de7ec6c1c499693934fb17610f69554c37d26` |
| Proof handoff | `f4bf98e96f799a4044d6d012e4854dc937b099005f25c3a20932757bcb6fbe2e` |
| Luna source-owner report | `cfcd2c910c1f74221a654954d99c02c0bea05f940c20adae3f66bcf4a4b15b3b` |
| Luna implementation handoff | `477d1cdfbf42afc8a06bed78fb95bc5ee90c5486d2e35ff0e30428ed6fae9049` |

All five target hashes and all nine direct contract dependency hashes matched.

## Review findings

Independent source inspection supports the constructor-specific no-hit claim:

- `Capture::row` deduplicates rows against the unchanged representative forest.
- `route_candidate_local_run` immediately reconstructs its fresh capture.
- Capture/accounting, `begin_use`, scope remapping and fresh allocation do not
  union existing keys before reconstruction finishes.
- The row loop therefore samples pairwise distinct source representatives; by
  induction each lookup in the initially empty canonical map misses.
- Bound restoration begins after the loop, so later merges cannot change the
  recorded hit flags.

The separate temporal-evidence gap is supported by merge/compression/rollback
owners: current representatives and rollback-restored generation do not retain
the reconstruction-to-inspection history. Committed undo information is
released.

The exact falsifiers are appropriate: demonstrate an authentic intervening
representative-changing operation, duplicate captured representatives, or an
exercised helper path reconstructing an older graph. A synthetic graph or final
equivalence class would not falsify this constructor-specific argument.

The reviewed outcomes are **FIXTURE_UNREACHABLE** and
**MISSING_RETAINED_EVIDENCE**, each static and bounded. This does not certify
fixture execution, universal impossibility of map hits, native transport,
source formation or theorem closure. Parent remains **OPEN, 0 → 0**. No test is
authorized because the required positive witness is absent.

Observed model/effort: **UNKNOWN/UNKNOWN**. No files written; no tests, runtime
probes, Git or delegation. Reviewer reports **WRITES_STOPPED; NO_DESCENDANTS**.
