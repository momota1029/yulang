# Sprint contract — EFFECT-PERMISSION-MODULE-MATERIALIZATION/r4

Status: **ACTIVE**. Baseline: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`
on worktree `yulang3`. This sprint resumes the unchanged source-rule audit
after r1/r2 pin/interpreter blockers and r3 aggregate-read truncation. Those
failures establish no supplier result. Preserve all prior artifacts.

## Goal and authority

Audit the adopted module-reference materialization rule and the two exact
module Call suppliers: source lane audits supplier correspondence; proof lane
independently audits applicability and circularity. Determine only whether the
admitted evidence discharges either supplier, and identify exact remaining
premises. Do not enlarge the source domain or admit another owner. Preserve the
original parent quantifiers, shared witnesses, callback → Call result → tuple
`left` obligation, all native/source obligations, and every production gate as
OPEN unless the assigned evidence actually closes it. No code slice is
authorized: `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding.

Read these governing files before the audit, one file or page per tool response:
`AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`,
`.agents/skills/yulang-lean-proofs/SKILL.md`, and this contract. Then read only
the admitted source/rule/parent/owner inputs required for the assigned question
from the pinned manifest. Do not batch body reads.

## Exact read protocol

All lanes must first run the exact bootstrap and preflight command supplied in
the primary's dispatch message from the repository root. The dispatch pins
this contract's final SHA-256 in that command; this file cannot contain its own
digest. No source/design/handoff body may be read before both
stages exit 0. Bootstrap verifies the current contract, manifest, preflight
script and prior r3 outcome/receipts; the script validates all 21 source pins.
Record both command results in the handoff.

After authentication, inspect at most one file/page per tool response and at
most 4 KiB per page, with output allowance at least 8,192 tokens. Record each
file hash, exact page boundaries (line numbers or byte offsets), and the next
continuation point. Do not aggregate independent file bodies. If a page is
truncated, discard it and retry a smaller bounded range; at most two smaller
retries are allowed for that page. Verify complete coverage before relying on
the file. Stop on two failed retries, any coverage gap, hash mismatch, exhausted
budget, or any other unauthenticated input. Never infer a conclusion from a
partial page. This controlled retry rule supersedes r3's stop-on-any-transport-
truncation rule for this contract only.

## Exact inputs and lanes

Manifest: `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json`
SHA-256 `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`.
Preflight: `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py`
SHA-256 `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`.
Prior STOP records to authenticate before reads:

```text
tasks/agent-loop/history/effect-permission-module-materialization-20261028-r3-outcome.md d5cbc467384922c6048efeb44999c1283ba89c6a3c81353cc385020d07e5efd9
tasks/agent-loop/inbox/effect-permission-module-materialization-r3-source.md 76e2b6edb486485cc8bfac35e0780e15a103d1768f09d9ba9e6f71b9db8c5d25
tasks/agent-loop/inbox/effect-permission-module-materialization-r3-proof.md 3c90dd78b24bc699c6abd088ff302feb6147de8e7ebac9c7337bc72a3a584721
```

Bootstrap and preflight command template (primary supplies the final contract
digest in the dispatch message; run that literal command verbatim, from
repository root):

```sh
set -euo pipefail
/usr/bin/sha256sum -c <<'R4_BOOTSTRAP'
<R4_CONTRACT_SHA256_FROM_PRIMARY_DISPATCH>  tasks/agent-loop/sprints/effect-permission-module-materialization-20261028-r4.md
aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11  tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json
7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133  tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py
d5cbc467384922c6048efeb44999c1283ba89c6a3c81353cc385020d07e5efd9  tasks/agent-loop/history/effect-permission-module-materialization-20261028-r3-outcome.md
76e2b6edb486485cc8bfac35e0780e15a103d1768f09d9ba9e6f71b9db8c5d25  tasks/agent-loop/inbox/effect-permission-module-materialization-r3-source.md
3c90dd78b24bc699c6abd088ff302feb6147de8e7ebac9c7337bc72a3a584721  tasks/agent-loop/inbox/effect-permission-module-materialization-r3-proof.md
R4_BOOTSTRAP
/usr/bin/python3 tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json
```

Source worker: `/root/effect_permission_module_materialization_r4_source`,
`researcher`, requested Sol/high, read-only. Exact output:
`tasks/agent-loop/inbox/effect-permission-module-materialization-r4-source.md`.
Audit the adopted source-rule text against the two named module Call supplier
owners and report direct evidence, gaps and exact scope. Do not write any other
path or make a negative claim beyond the inspected owners.

Proof worker: `/root/effect_permission_module_materialization_r4_proof`,
`lean_prover`, requested Sol/high, read-only. Exact output:
`tasks/agent-loop/inbox/effect-permission-module-materialization-r4-proof.md`.
Independently assess the same source rule's applicability, circularity and
whether its premises are supplied without assuming the conclusion. No Lean or
Lake execution, theorem construction, or axiom claim is requested.

Fresh independent reviewer: compiler_referee, read-only, after both frozen
handoffs. Review authentication order, page coverage, exact rule-to-owner
correspondence, quantifier preservation and whether conclusions stay within
the observed domain. Return the review as a collaboration receipt; primary
records its compact disposition in
`tasks/agent-loop/inbox/effect-permission-module-materialization-r4-review.md`.

## Resource and stop bounds

R1/r2 are charged 1,400 seconds. Charge the full 700-second r3 reservation
conservatively (including both 200-second producer grants); remaining ceiling
before r4 is 5,100 / 7,200 seconds. R4 total grant ceiling: 500 seconds:
source 150, proof 150, review 100, primary 75, contingency 25. Charge grants
fully; no refunds, reuse, descendants, Astra, Cargo, tests, builds, Git, or
compiler/source edits. Every leaf must stop and freeze only its assigned
receipt at its cap or a stop condition. Any follow-on needs a new selector
decision, fresh exact paths and a new grant.

## Completion and shared state

Close this sprint as `CLOSED_INCOMPLETE` if either lane cannot complete the
authenticated bounded audit. A fresh reviewer must inspect the completed
receipts before any semantic disposition is adopted. At closure, record exact
hashes, page coverage, runtime/charge evidence, review verdict and open gates.
The module Call suppliers and all parent/native/production obligations remain
OPEN absent direct accepted evidence. Keep all legacy UNKNOWN reservations and
quarantines; do not alter frozen `main`, use Git, or promote a conditional
lemma, tooling receipt or finite observer to parent closure.
