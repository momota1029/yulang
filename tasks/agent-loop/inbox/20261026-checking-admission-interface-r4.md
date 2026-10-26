# Goal-indexed checking admission: frozen interface checkpoint

Status: AUTHOR FROZEN, independent review pending. No further writes to the
three source files below without the primary's explicit dependency HOLD.
The separate new admission module and final note/handoff remain AUTHORING and
are excluded from this checkpoint.

Baseline supplied by primary: `ff12ce5049cb7f26c7d873467c9a761ed49fc3e1`.
Packet started 2026-10-26 14:08:15 UTC; deadline 15:08:15 UTC. This checkpoint
uses checks 1–3 of the same 28-call budget. Core freeze: 14:13:57 UTC.

## Exact frozen sources

| Source | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `0f25e53350edf9c452fd3c0f461602437ca2adf979859fda5e2492bcc403ae55` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |

Generation was independently frozen after check1 and released to the primary
for PairK. It has not changed since that release. All three final sources
equal their exact check2 and check3 snapshots.

## Claim and original source correspondence

SG §3.2(4) requires each finite Function checking node to inspect its own
checked domain, including intermediate targets of logical composition.
`OriginalSource.Kernel.checkingAdmitted` now receives the enclosing CheckGoal.
Its explicit default is the old `admitted` relation, independent of that goal.
Only `Checking.function` uses the new field for its observation child.

All source forall/exists/execution/shared admission expressions remain
byte-identical, as do sourceRules, clientRules, generated Formula/compile,
raw actual-event keys, binder arity, runtime payloads and source operands.
This is conservation of source admission telescopes, not an assertion that
all source judgments stay equivalent after intentionally correcting local
Checking semantics.

The existing Environment admissionKernel and functionKernel deliberately
install legacy checking admission explicitly alongside original admission.
Record updates do not recompute a previously stored default. The new
goal-specific override must be applied AFTER those wrappers; the separate
module will prove both final admission projections and composition order.

The registered proof Kernel preserves both admission fields. FunctionLeaves
and FunctionShape retain the enclosing CheckGoal and use that Kernel's exact
checkingAdmitted predicate. The finite Checking.rec proof now consumes the
recursive observation IH at that predicate and goal. Other structural and
primitive constructors, direct actual Boundary, and all previous theorem
names remain present. The old Environment current-event theorem remains the
explicitly legacy conditional theorem with targetReadback.

## Record-update census

Only Environment.admissionKernel and Environment.functionKernel overwrite
source admitted; both now explicitly install legacy checkingAdmitted.
Interpretation.literalKernel/nameKernel and Environment.foldedLiteralKernel/
foldedNameKernel update only atom and preserve both fields. Checking.kernel
updates its three proof-schema fields, preserves both admission fields, and
uses original.checkingAdmitted for the Function proof leaves.

## Checks and complete audit

Pinned native toolchain: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb`. No installation, packages, shared configuration or global
default changes. Native execution uses the authorized exact local distribution.

All checks use an owned isolated project, one CPU affinity, one Lean thread,
`-j1 -M1024`, a 120-second process-group deadline, and a monitored 1280 MiB
aggregate process-group RSS ceiling. All actual snapshots are retained from
check1. Check2 built OriginalSourceChecking and OriginalEffectHygiene with their
imports; check3 audited the three changed module origins. All three calls
exited 0 with no errors or warnings. No failure or timeout occurred.

| Origin | All originating declarations | Theorem constants |
| --- | ---: | ---: |
| OriginalSourceGeneration | 819 | 355 |
| OriginalSourceEnvironment | 753 | 289 |
| OriginalSourceChecking | 827 | 299 |
| Total | 2399 | 943 |

All 152 previously authored theorem roots were required to remain theorem
constants. Every originating constant, including private/generated constants,
has its complete type and #print axioms output in the census. No project
axiom or unexpected axiom was found. Actual standard axiom union:
`propext`, `Quot.sound`, `Classical.choice`; per-constant results are retained.

Evidence:
`/workspace/scratch/f98087c7ac1a/checking-admission-r4/core-freeze/`.
It contains the frozen sources, exact changes.patch, full 03-census.log,
CoreAdmissionAudit.lean, per-constant axioms.json, all required root names,
tool versions, initial input manifest and build log. The adjacent
core-freeze.json records all hashes. checks.json contains commands, actual
snapshot manifests, elapsed time, peak RSS and log hashes. No shared default
integration build is claimed; that remains primary-owned.

## Limits and continuation

This interface checkpoint does not yet supply concrete goal admission,
no-targetReadback observation transport, or the nonconstant nested-domain
discriminator. Those constructions continue only in OriginalCheckingAdmission
and the new packet's own note/handoff/scratch. No blanket KernelSound or new
safety predicate is introduced. Future-event FunctionShape registration,
original primitive/structural/native registry correspondence, and general L4
remain separate obligations.

Core source writes STOPPED. No checker process remains running at this freeze.
No descendants or Git operations were performed. Primary owns independent
review, integration, shared status, commit and push.
