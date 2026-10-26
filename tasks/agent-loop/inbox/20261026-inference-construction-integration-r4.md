# Inference construction integration — primary producer receipt

Author: `/root`. Target: `momota1029/yulang`, `yulang3`.
Status at freeze: constructed and checked, pending fresh nonauthor integration
review. Full original inference soundness remains OPEN.

## Exact write surface

Only the following new integration files are in this packet:

- `notes/theory/lean/YulangClosure/InferenceConstruction.lean`
- `notes/theory/lean/AuditInferenceConstruction.lean`
- `notes/theory/2026-10-26-inference-construction-integration.md`
- this producer receipt

The primary progress ledger and later publication metadata are separate primary
records. The unknown foreign `InferenceProofs`/`AuditInferenceProofs` writers keep
their leases. No root/configuration/manifest/Rust/expected-output path is edited.
The ongoing WorldReadout packet is excluded from this fixed integration snapshot.

## Reviewed component boundary

The final component baseline is `5428c5e62e31b20f261c76128cf426fdd137cca5`.
The newest own components are separately published and independently reviewed:

| Component | Published commit | Fresh review SHA256 |
| --- | --- | --- |
| Current-goal admission | `99f18bdc54df8057f5a6d5d4bec5dc449336c234` | `3e8fb7ec9ec5ef6f85e60e647bc867def210f00c5bc191e0a2890928e4f98f1b` |
| Actual future observation | `3be95e44e203f9bf522576fc7ff1a5a889fbe046` | `afa740323ba83d1d5b2e96ce4cca938eb827b5e5128fc9cc1cbb8f9a262726d5` |
| Selected recursive pair | `5428c5e62e31b20f261c76128cf426fdd137cca5` | `e98b15e581ea961db82b65d884df4315d6bbf2bbeb7583a165c3de8fdf50b1d8` |

All previously integrated r4, independently published r5 and eight foreign
WholeMetatheory components retain their individual author/reviewer evidence.
The integration note states the actual constructive progress and remaining
source/native/owner obligations. It does not assert whole `KernelSound`, complete
source registrations, selected recursive Knu closure, general L4, original
principality/termination, or complete inference soundness.

## Exact execution and bounds

Owned project: `/workspace/scratch/f98087c7ac1a/final-validation-r4/project`.
Native Lake:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Versions: Lean4.35.0/eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake5.0.0-src+eb6cafb. No external packages or configuration changes.

The bounded runner is `final-validation-r4/run_validation.py`. Its build mode
executes native `lake --no-cache build +YulangClosure.InferenceConstruction
YulangClosure`. Its audit mode executes native `lake --no-cache env lean -j1
-M1536 AuditInferenceConstruction.lean`. All inputs are hash-checked before each
command. Both modes use one CPU/thread and an exclusively owned cache/TMPDIR.
Build:240s/6144MiB aggregate; audit:120s/2048MiB aggregate. The audit's per-Lean
1536MiB cap is local to the full printed census; normal module builds retain
the existing -j1-M1024 configuration. The runner monitors child-process RSS,
records exit/termination and drains output completely.

Actual environment: normal sandbox Lake startup fails to locate its installation.
The permitted require_escalated execution of the exact fixed bounded runner
succeeds. No automatic approval rejection, changed dependency, alternate
toolchain or runtime security bypass was used. The failed startup and blocked
read-only ptrace diagnostic remain recorded separately.

## Final successful results

| Evidence | Result / SHA256 |
| --- | --- |
| Build04 | Exit0,127jobs,19.572692s,peakRSS1019449344 |
| Build04 log | `7cbb3a1c9c4530974fff12a07c2b876112131b10b48812f7a817879a2289fc3c` |
| Audit06 | Exit0,40.909217s,peakRSS1387986944 |
| Audit06 log | `b099631169834f6dc00a380918ff794bc90f81f78c5058675474c97cbbc99e2b` |
| Checked input manifest | `76907c0ab43ae59e888fa3304e633abc35cf9f7edc7664ce8ec2e9aff2ad8ece` |
| Census | 64 origins,9595 unique theorem constants,1640 required roots |
| Input closure | 129 exact Lean/configuration inputs |
| Standard axiom-set counts | none5199;propext2396;Quot.sound8;propext+Quot.sound1521;all3standard471 |

`verify_census.py 06-qualified-pair-roots-audit` exited0. It checked all balanced
record markers, theorem/root uniqueness, exact origin counts, full untruncated
types, normalized transitive axiom sets, worktree and snapshot input hashes,
and both protected root/scheduling hashes. The complete records and the verified
summary are stored with that audit prefix.

`origin-census-reconciliation-through-17.json` reconciles every new isolated
theorem name against the full combined records, including generated names with
earlier imported origins. Record307 adds256 unique; Pair240 adds237 unique.
Admission65/Future24/Progress50 all remain present. Earlier Table/Interner/Effect
reconciliations are retained. Different pretty-print settings are not mislabeled
as byte-identical type reports; exact names and normalized axioms are compared.

`warnings-reconciliation-through-17.json` verifies all668 warning first-lines
against both preceding accepted logs, with identical multisets and nine exact
unchanged source hashes. The prior empty-counter receipt from an over-escaped
pattern remains preserved and is explicitly superseded. No new warning appears.

## Failure history retained

- Build01 failed before Lean at native Lake installation detection; it is not
  counted as mathematical checker success.
- Audit03 kernel execution passed; its first naive isolated-count postprocessor
  failed8965→8963. Two generated-name origin duplicates were reconciled without
  altering proof terms or rerunning Lean to disguise the discrepancy.
- Audit05 failed because all69 Pair required roots were unqualified short names.
  Audit06 fixes only those names. Build04 inputs and final inputs differ only in
  this standalone audit source, which is not compiled by the build target.
- Every previous snapshot and failed log remains immutable under `snapshots/`.

Current source/config snapshot:
`final-validation-r4/snapshots/03-qualified-pair-roots/inputs`.
Previous snapshots01/02 include their complete exact input copies and metadata.
The pending-review labels in snapshot02 are historical; both components now
have the independent receipts above. No immutable snapshot is rewritten to
pretend those reviews were already complete at the earlier time.

## Proof-closure and source boundary

The exact parent remains original `SourceProblem.InferenceSoundness` and the
successful native correspondence, with full supported grammar and the same
joint scoped witness. The integrated local components do not instantiate these
whole roots. The note records current future-event domain/action mismatch,
missing formal rebind retained Shared/EventField ownership, actual decorated
world/Return correspondence, full recursive phase and hole replacement, and
remaining primitive/full source/native obligations.

In particular, SG3.3's retained initializer/rebind Shared evidence is not erased
because the present Lambda generation lacks a dedicated sharedE there. A current
formal representation omission is not original semantic authority. The active
new constructor lane is isolated from this accepted snapshot and must supply
the missing owner or report its precise boundary.

## Freeze and handoff

The external `final-validation-r4/integration-freeze.json` records this receipt,
the other three leased files, every129 checked input, successful/failed logs,
full records and reconciliations. It is written after this receipt to avoid a
self-referential hash. Source/audit/checker writes for this snapshot stop at
that freeze; no owned runner/Lake/Lean process remains. The continuing distinct
WorldReadout worker has no write lease on these files or the isolated cache.

A fresh nonauthor reviewer must inspect the full integration mechanism, input
identity, all counts/roots, origin reconciliation, complete axiom output, source
scope wording and preserved failures. It may independently run a bounded check
in its own cache if needed. It must not treat its prior component review as
mathematical authorship or imply that aggregate counts prove the parent theorem.
Only the primary may adjudicate, stage these exact paths and publish.
