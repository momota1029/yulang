# R71 Luna owner-map handoff — revision 1

Sprint / contract: `raw-canonical-fiber-coverage-20261019-r71`, revision 1, SHA-256 `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`.
Baseline: `f375fd737`; 20 direct dependency pins MATCH at activation.
Owner: `/root`, Luna/high, current session `current-conversation-2026-10-19-r70-extrusion`.
Exact leases: `notes/progress/2026-10-19-r71-fiber-owner-map.md`; this handoff.
Outcome: source/native owner map only; no proof, source-qualified counterexample, semantic choice or code authorization.

Route: R70's two production extrusion callers -> physical selected Value/Effect bounds -> `Work::Bound` (canonical child key, stored source `BoundKey`) -> copied physical append/readback -> exact-key contextual fiber transfer -> exact-key origin metadata loop -> representative merge and global bound-key canonicalization. The map separates physical slot, exact raw source, canonical child/target, contextual relation chain and diagnostic-origin vector. It records that appends canonicalize at time of insertion, physical vectors remain stored across later merges, merge transfers before writing the representative edge, and global canonicalization transports existing bound keys while retaining originals, including third-party owners.

Result remains open: establish a constructor-derived inclusion for each reachable physical source slot, or provide a production-reachable missing-fiber trace. Per-key fiber equality is not presumed. Keep R70 entry-WF, source reachability, later drain/ack, source/evaluator correctness and parent/A/B claims separate. The countertrace author had sent only an interim static direction at map freeze; it is not adopted as a result.

Checks: exact R71 pinned source reads and static path mapping only. No tests, builds, probes, compiler/source execution, Git operations or source changes by this lane. Luna will perform the final 20-pin/hash verification before freezing.

Writer state at handoff: `/root` remains the sprint coordinator. These two map outputs freeze when Luna records their final hashes and marks their leases FROZEN. No descendants.
