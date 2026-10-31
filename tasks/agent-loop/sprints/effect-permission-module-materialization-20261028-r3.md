# Sprint EFFECT-PERMISSION-MODULE-MATERIALIZATION/r3

Status: ACTIVE after frozen fail-closed launcher preparation. This continues the
same fixed audit; r1/r2 contracts and blocker receipts remain immutable.

## Outcome and boundaries

Determine whether revision-2 `ModuleEnv-Expose*` clauses noncircularly discharge
(1) ModuleDef Name/DefinitionUse → selected Definition-entry typing/admission,
and (2) that entry's receiving/export correspondence → actual Call callee. Give
an applicable derivation or the first exact missing premise for each supplier.
`AUTHORITY_BLOCKED` is not impossibility. Preserve the original parent
universal source/history/occurrence quantifiers, shared lawful witnesses, and
soundness/progress/principality/termination duties. Callback → Call result →
tuple component `left` remains separate. No semantic, source-domain, compiler,
fixture, expected-output or production change. Preserve
`DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` and every UNKNOWN/quarantined path.

Worktree/baseline: `yulang3` / `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`.

## Bootstrap and exact preflight

Bootstrap files (hash these before executing the preflight):

- This contract: its SHA-256 is supplied in the dispatch and independent review.
- Manifest `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json`, SHA-256 `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`.
- Script `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py`, SHA-256 `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`.

Runtime resolved by Luna: `/usr/bin/python3`, Python 3.12.3; checksum tool
`/usr/bin/sha256sum`. Working directory is the repository root.

Every producer and reviewer must run the following command verbatim, replacing
`<CONTRACT_SHA256_FROM_DISPATCH>` with the exact contract digest supplied by
Luna. Shell `set -euo pipefail` makes any failed bootstrap check stop before the
Python manifest reader runs. The reader validates all 21 digest strings and
paths before hashing; it prints path/hash/status only and exits nonzero on any
mismatch. Do not inspect any manifest-listed body until the complete preflight
prints `PREFLIGHT_21_ENTRIES_ALL_MATCH`. Any tool error, malformed digest,
missing path, mismatch or truncation means STOP with no fallback or excerpts.

```sh
set -euo pipefail
/usr/bin/sha256sum -c <<'R3_BOOTSTRAP'
<CONTRACT_SHA256_FROM_DISPATCH>  tasks/agent-loop/sprints/effect-permission-module-materialization-20261028-r3.md
aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11  tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json
7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133  tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py
R3_BOOTSTRAP
/usr/bin/python3 tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json
```

## Admitted manifest

The JSON manifest contains exactly 21 pins: the exact revision-2 rule; its
adoption decision; original parent §§1, 3, 5; five native files
(`candidate_call`, `candidate_source`, `candidate_scheme`, `shadow_apply`,
`lib.rs`); seven previously admitted design owners; r1/r2 blocker receipts and
outcomes; and the prior environment source/proof/outcome handoffs. Their exact
paths and SHA-256 values are in the hash-pinned manifest above. Admit no other
linked document implicitly. R1/r2 receipts show only pin/tool blockers; the
r1 proof lane's previously recorded read-sequencing deviation remains explicit.

## Lanes and output leases

**Source — fresh read-only `researcher`:** after its successful exact preflight,
map actual revision-2 rule premises/conclusions to both suppliers and the
selected Definition entry/Call callee. Distinguish rule conclusions from
required premises; assess identity/scope/recursion/import/capture only as
represented. Write only
`tasks/agent-loop/inbox/effect-permission-module-materialization-r3-source.md`.

**Proof — fresh `lean_prover`:** independently preserve parent quantifiers and
shared witnesses; audit applicability/circularity against the exact native
equations and name the first unsupplied premise per supplier. Write only
`tasks/agent-loop/inbox/effect-permission-module-materialization-r3-proof.md`.
Create `notes/theory/lean/YulangClosure/FormalPermissionModuleMaterializationR3.lean`
only for a useful sourced derivation. No Lean/Lake run absent separate primary
release after complete input freeze.

**Review — fresh nonauthor `compiler_referee`:** rerun the exact preflight, then
review frozen handoffs and any claimed supplier discharge. Return a read-only
final receipt to Luna; Luna records it at
`tasks/agent-loop/inbox/effect-permission-module-materialization-r3-review.md`.

## Resources and stops

Cumulative cap 7200 seconds. R1 and r2 full grants remain charged: 1400 seconds.
R3 reserves at most 700 more (source 200, proof 200, review 150, primary 100,
contingency 50), leaving 5100 seconds; no refunds/reuse. At most two producers,
zero Astra, no Cargo/tests/build, one verifier. At most one Lean audit ≤120s and
≤1 GiB only after separate Luna release. No descendants. Stop at any failed
preflight, new unadmitted dependency, circular supplier premise, budget boundary
or user STOP. All parent/native/Call/effects/principality/termination/production
gates remain OPEN unless independently discharged.
