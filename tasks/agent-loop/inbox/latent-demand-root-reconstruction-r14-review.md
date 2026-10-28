# R14 independent review receipt

Assignment: fresh review of the frozen native representation candidate.
Reviewer: `/root/latent_demand_root_reconstruction_r14_review`, distinct from
the implementation author. Verdict: **ACCEPT — bounded native representation
candidate only**. No BLOCKING, major or minor correctness findings in the
authorized diff.

## Authenticated inputs

| Artifact | SHA-256 |
| --- | --- |
| Contract revision 2 | `caf7474b5c34046bad8ff8599915dc2e1bc6d6aaf2cc28dbaff27509d9a06d91` |
| Amendment 01 | `b164d7e216715e9a89e2a09f78e863afc5536b76833bae58a50536545396b5cf` |
| Manifest revision 2 | `a07d873f38e1abf3be5eb86700d2942c156bff2f09a83dc62ec88f450ef0e395` |
| Proof handoff revision 2 | `b1e1253dbbb3ea918e8782619ba2a8bddfeba2842a2d84d80790eba0130ac17c` |
| Implementation handoff revision 2 | `919451075e40c90a060fdd29473cbc228057e1b71eb4176e367fcc42911f29ce` |
| Candidate | `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0` |

All eight parent pin objects matched. Of 334 file pins, 331 matched the
original hashes; the three expected successors were the candidate and the two
handoffs and matched the supplied frozen hashes. The reviewer authenticated
the R13 baseline candidate (`0ca44b920d30e0a596584c9c4ad5e2a61fdd9115fe1eaaf4346ff64d0776afef`)
and inspected the complete candidate diff.

## Review findings

- Capture already interns each demand attached to a captured bound. The new
  publication block retains that exact same-graph endpoint index and realizes
  `M' = I|(F∪D)` without fixture, root-number or graph-number special cases.
- The root must be a negative Function; its endpoint must exist in this
  capture; its node must be a negative Function; a conflicting entry fails
  closed. Existing formal entries remain unchanged, and an overlapping root
  must resolve to the same index.
- Existing formal permission projection still requires source-owned permission
  records, formal-domain ownership and the typed permission path.
- Relation/use incidence and all existing route, original-call, scope/input,
  evidence, polarity/four-port, FreshUse, fiber/readback and Replay checks
  remain in place. A shared structural root does not merge independent uses.
- Added allocation is fallible and the retained map capacity remains included
  in graph accounting. A failed capture is not published.

The reviewer inspected the unchanged focused fixture and sibling
shared-reconstruction test as source only. No tests, Cargo, builds, Lean or
checkers were run by the reviewer. Reviewer files, Git state and background
processes were untouched. Exact launch-relative elapsed/CPU/RSS were
unavailable; final observed time was `2026-10-28 12:11:42 UTC`. Reviewer
STOPPED.

## Scope boundary

This receipt accepts only native capture-to-reconstruction representation.
It establishes no source Call/Generalize adequacy, source allocation law,
shared-witness correspondence, antecedent eligibility, effect hygiene, parent
soundness or production readiness. Those gates remain **OPEN**. The contracted
unchanged fixture check is reported separately in the R14 outcome below.
