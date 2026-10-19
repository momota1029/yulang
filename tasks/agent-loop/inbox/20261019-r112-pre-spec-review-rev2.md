# R112 revision-2 pre-edit specification review

Status: **major — STOP pending exact output-lease reconciliation**.
Reviewer: `/root/r112_pre_spec`. No producer work or theorem certification.
Contract SHA-256 matched `a2a5f3a018d3a2385484f499b31637c816c2cade92a4a5bef3f10045da2e97c1`.

## Finding

- **major; contract inconsistency, not an implementation defect or approved semantic change.** Target: `tasks/agent-loop/sprints/method-role-p2-source-application-20261019-r112-rev2.md:100–101`. The fresh pre-edit review still leases the rev1 receipt path, while lines 87–90 preserve that existing receipt and explicitly say it does not clear rev2. Luna's current assignment correctly directs this reviewer to the distinct revision-2 receipt path, but the frozen contract does not express that lease. Authority: root `AGENTS.md` §Preserved non-negotiable boundaries (“Only the primary grants exact leases”) and revision-2 contract §Frozen inputs, lines 87–90. Closure: Luna reconciles the contract's exact pre-edit output path with the distinct rev2 receipt, preserves rev1 bytes, and obtains a delta review of the resulting frozen contract. This reviewer does not repair the contract or approve its replacement.

## Completed checks before stop

All nine input pins match, including the added R100 implementation assessment at `tasks/agent-loop/inbox/20261019-r100-implementation.md`, SHA-256 `60a1a90c37b5c8377addf12cd07d9703f98a093a9c1eeb86fb5db2b81f847596`. That assessment remains historical NO_SAFE_ROLE_CODE_SLICE evidence with no code authority. Its revision-4 provenance is explicit and is not relabeled as a revision-6 assessment.

The literal fixture and all substantive outcome, source-to-parent, falsifier, stop, no-command, resource and breadth clauses are byte-identical to reviewed rev1. The prior exact 148-byte/hash inspection therefore remains applicable. The allocation still sums to 600 seconds with 60 seconds shared across pre/post spec review; it is not a new allocation per review revision. R111 quarantine, no retry and spent/unknown resources remain preserved. R85 remains Draft/unadopted, with original A/B, F1/FK1, R50, six effect fronts and adoption/production boundaries unchanged.

No expected-output, fixture, diagnostic, golden, snapshot or semantic test-name change is leased. `rules/testing.md` §Expected-output protection and `rules/design-authority.md` §§Approval and implementation gate, Test contracts continue to govern any future change. Current output or green tests establish no semantic authority.

Static text/diff and frozen SHA-256 inspection only. No test/build/compiler/runtime/CLI/formatter/Git command, producer work or descendant. Only this directly assigned receipt was written. STOP at the finding; no repair.
