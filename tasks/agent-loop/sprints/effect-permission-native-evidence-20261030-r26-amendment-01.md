# R26 amendment 01 — bounded Lean memory guard

Sprint: `ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R26`. This is a resource-seam disposition under the admitted contract; it does not change its objective, semantics, assignments, leases, total time, audit count, or source authority.

Evidence reviewed: R26 active receipt SHA-256 `86f33d299e555ff06e30793873801102e13b5ee06606e85d8ff13f8708c45852`; Lean module SHA-256 `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`; audit 1 log SHA-256 `bd95bb5cb08c1a8151f2096098e3cd3444a568a0b15aa358bc72cc9c3aee207e`; resource record SHA-256 `774829a9c74472d73dc75079dcd35c72a139d01aae5d65cfedb3630c17e46816`. Audit 1 built the module with pinned Lean 4.35.0, then exited 130 after 8.063953784 seconds when the external process-tree RSS guard reached 1,109,495,808 bytes. Four declaration type/axiom blocks are complete; the full audit remains incomplete. No process remains.

`/root/next_action_selector` recommends a single local increase of the external process-tree guard to **1,342,177,280 bytes (1.25 GiB)** for audit 2. Its reasoning is the measured 1.033 GiB peak, exclusive heavy-process window, and 663 GiB available host memory. Luna approves this narrowly bounded adjustment before execution.

Audit 2 may run once, for at most 90 seconds, and never beyond the 111.936 seconds remaining under the combined 120-second audit cap or the assignment's actual remaining time after handoff reserve. Preserve the same frozen module, dependency hashes, pinned checker/toolchain, Lean `-j1`/`-M1024`, CPU limit, exact theorem list, and axiom requirements. Reuse audit 1's four complete blocks only if module, dependency and toolchain hashes still match; preserve their separate provenance. Keep the heavy window exclusive; no Cargo overlap.

If audit 2 exceeds this amended guard, fails, times out, or omits any requested theorem type/complete axiom report, preserve the raw evidence and stop. No third attempt, further memory increase, or budget renewal is authorized. A complete audit remains subject to independent review and source/native applicability; it does not close the parent or production gate.
