# Sprint choice-a-carrier-and-diagnostic-contract-repair-20261017

Status: ACTIVE, Luna-admitted at baseline `1a14f115ec3811f8f8133a09027ce9b5d6ad359d`.
Branch: `research/simple-sub-intrusion`; contract revision: 1.

## Parent and bounded outcome

Parent remains the original Yulang inference/execution goal with all original
A/B claims, quantifiers, source/native correspondence, F1/FK1, N-Transport,
complete Call, soundness, principality, termination and production gates OPEN.
The predecessor sprint `ordinary-hir-choice-a-contract-20261017` is closed
REVIEWED-PARTIAL: its fresh spec review found two MAJOR contract conflicts.
Those findings do not close any original theorem condition.

Outcome: repair the exact direction-A ordinary-HIR successor proposal to preserve
the adopted ordinary `LocalSource` carrier contract and to state a consistent
Error/Diagnostic-ID compatibility rule under dense per-module indexing; then
obtain sequential fresh spec, compiler and architecture reviews of the repaired
bundle. The frozen 48-pin source/CST audit is reused without rerunning or
widening its source domain. Direction A authorizes this proposal repair/review
only. Final user approval of the exact reviewed text remains required before
any compiler or test work.

## Exact baseline and dependencies

Baseline: `1a14f115ec3811f8f8133a09027ce9b5d6ad359d`.

Frozen source audit:
`notes/theory/2026-10-17-choice-a-call-cst-source-key-audit.md`, SHA-256
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.

Direct implementation pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
notes/design/2026-10-10-ordinary-hir-successor-carrier.md c5fb75bdeb302a1f490398589b823f26d296d4cff3889cd0fddd5be4f801dad1
```

All other prior source, parser, API and theorem dependencies remain those
pinned by the predecessor contract rev4; no source-domain expansion or new
semantic premise is authorized.

## Findings to close

1. Preserve one existing ordinary `SourceCarrierOutcome` per admitted binding,
   including its Supported/Unsupported distinction and current source/artifact
   identity behavior. Specify how ordinary accepted Apply nodes and their
   source keys relate to those carriers. Preserve all old carrier occurrence
   ordinals by completing ordinary carrier allocation before allocating any
   new HIR-only application child occurrences. HIR and LocalSource projections
   may have distinct branded occurrence IDs for the same exact parse key; do
   not promise ID equality across these representations. Keep atomic publication
   and existing availability failures.
2. Preserve dense, phase-local, internally valid error/diagnostic IDs and
   exact retained record contents, attachments and contract-defined ordering.
   Explicitly state that removing an application admission error and introducing
   newly visited operand errors may reindex later records; numerical equality
   across pre/post-admission module products is not guaranteed unless a specific
   identity is independently justified. Define retained-record correspondence
   by full record payload and order/multiplicity, not its numeric index. Do not
   add sparse IDs, tombstones, or a new storage scheme. Name the precise
   predecessor clauses whose application behavior is superseded and expose this
   observable consequence for final user approval.

If the source-carrier requirements leave multiple materially different identity
policies, record that exact unresolved choice in the proposal and stop before
review/adoption rather than choosing silently.

## Leases, roles, budget and sequence

Luna is the sole author/integrator, up to 240s, with exact writes to:

- `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`
- `tasks/agent-loop/inbox/20261017-ordinary-hir-application-admission-successor.md`
- two immutable predecessor copies under `tasks/agent-loop/archive/` (created
  before revising the leased artifact).

After the author stops and the repaired bytes are frozen, run sequential fresh
independent reviews: spec auditor <=100s, compiler referee <=100s (including the
frozen source audit and exact implementation pins), architect <=100s. Reviewers
write no files. Repair blocking/major findings only within any unspent repair
budget; otherwise close REVIEWED-PARTIAL and return the exact choice. No author
reviews own work.

Cap: 720s total: Luna240, reviews300, coordination60, reserve120. No borrowing
from the predecessor sprint's retired 260s. Charge the predecessor spec review
at its conservative 100s and preserve its report. Keep three inherited UNKNOWN
leases/reservations quarantined; they are not writers and are not reclaimed.

## Non-goals and stop

No source/library/compiler/test edits or executions; no Cargo, builds, probes,
solver acceptance, source T, Call typing proof, original theorem closure,
production promotion or final semantic/API adoption. No tests are to be run.

Stop after the exact reviewed contract, a concrete unresolved identity choice,
budget exhaustion, a new indispensable dependency, or contradictory authority.
Final approval of the exact reviewed contract and named supersessions is a
separate user decision. Report: original theorem conditions genuinely closed
(0 expected); new compiler/test behavior (none); remaining proof gate and one
next cut.
