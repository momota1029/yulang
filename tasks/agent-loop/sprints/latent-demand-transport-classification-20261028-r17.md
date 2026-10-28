# LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r17 — per-row first-guard evidence

Status: **ADMITTED BY LUNA** under the standing inference/executor research authorization. R16 is CLOSED_INCOMPLETE; R17 is a new diagnostic packet, not a retry or semantic repair.

## Fixed objective and boundary

Record the first rejected stage for every actual replay row and matching FreshUse route in the frozen R16 candidate fixture. R16 established four same-invocation root joins and `session.execute() == Ok`, then failed because the emission evidence vector was empty. Its test selected call 0 as a unique row even though it had two rows (uses 1 and 3); this packet instruments the existing authentication loop that already visits all replay rows.

The only candidate-source delta allowed is in that loop: replace its call to the silent `authenticate_demand_transport` wrapper with the existing `authenticate_demand_transport_observed` core, passing the same arguments and collecting the same `Option<DemandTransportEvidence>`. Its observer may print row identity (call, use, child/lower/upper relations, root) alongside each existing `(owner, route, stage)` event. Preserve all arguments, evidence construction, guards, return values, and existing assertions. No guard, selection criterion, source fixture, expected output, feature, dependency, manifest, lockfile, production code, or semantic behavior may change. The observed core delegates to the same authentication logic; instrumentation is test-only evidence.

Goal is diagnosis, not repair: identify every actual row and each route's first rejection (or acceptance), including unmatched rows/routes and missing prerequisites. Do not attribute a general defect from one finite fixture. Preserve `EvidenceCoverage { gaps: 56 }` unless exact output changes it.

## Frozen baseline and complete input closure

Manifest: `tasks/agent-loop/sprints/latent-demand-transport-classification-20261028-r17-inputs.json`, SHA-256 `5ff66c9237154d5d15161d68871c06b94d1de3e935edc838f4781f5758a3c121`.
Snapshot: `isolated/latent-demand-transport-classification-r17/`.

The 446 manifest entries are byte-copied from R16's complete 438-workspace-file plus 8-governing-input closure; all bytes were rehashed. The manifest also pins 26 parent artifacts, including R16's contract, complete-input manifest, source/implementation/review receipts, outcome and all four Cargo logs. The Cargo.toml/Cargo.lock and focused test source begin at the R16 candidate baseline. The candidate baseline SHA-256 is `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.

R17 `build-target` must be absent before the one Cargo attempt. Logs are leased only as `isolated/latent-demand-transport-classification-r17/logs/r17-cargo-1.{argv,resources.json,stdout,stderr}`.

## Lanes, exact leases and budgets

Aggregate cap: **1,800 seconds**, no descendants and no Astra.

- **Luna primary — 600 seconds total.** Owns R17 contract/manifest/state, one Cargo attempt, fresh target, logs, integration and outcome. Cargo's 180 seconds count inside this grant.
- **Luna/high implementer — 300 seconds.** May edit only `isolated/latent-demand-transport-classification-r17/crates/yu-solver/src/candidate_scheme.rs` and `tasks/agent-loop/inbox/latent-demand-transport-classification-r17-impl.md`. Freeze the exact diff and STOP before independent review.
- **Sol/high source/proof — 600 seconds.** Stage 1 (up to 300 seconds): map source Call/use identity to every replay row and the authentication constructor/consumer, record remaining source/native premises and freeze rev1. After Luna ACKs rev1 and freezes Cargo-1 logs, resume within the same grant for row-specific trace-to-source mapping and rev2. Sole handoff `tasks/agent-loop/inbox/latent-demand-transport-classification-r17-source.md`.
- **Fresh independent compiler reviewer — 300 seconds.** Pre-run snapshot/diff/closure review up to 90 seconds, then STOP. Only after Luna ACKs frozen Cargo-1 logs may the same reviewer resume within the remaining grant for execution evidence. Sole receipt `tasks/agent-loop/inbox/latent-demand-transport-classification-r17-review.md`; the read-only reviewer returns its receipt to Luna for materialization.

No grant resets. Any changed pin, unclassified row, behavior-changing diff, review rejection, STOP or budget boundary prevents execution or closes this packet incomplete.

## One exact Cargo attempt

Only after fresh pre-run review **ACCEPT**, Luna may invoke exactly once:

```text
CARGO_TARGET_DIR=isolated/latent-demand-transport-classification-r17/build-target cargo test --manifest-path isolated/latent-demand-transport-classification-r17/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

Limits: wall **180 seconds**, CPU affinity **0 only**, process-group RSS at or below **2 GiB**. Capture argv/environment, Cargo/rustc versions, complete stdout/stderr, UTC start/end, exit status, sampled process-group CPU/peak RSS and any limit termination. No retry, alternative command, build repair, metadata, other test, or Lean run.

## Acceptance and source boundary

The bounded success result is an independently authenticated classification for each replay row and every matching route, including explicit `no matching route`, `no native call/ports`, acceptance, and the first rejected stage. No classification may rely on call-only uniqueness. R17 may establish an owner-specific evidence obstruction or a bounded observation; it cannot authorize repair or prove source adequacy.

The source receipt must map observed rows to source occurrence, Call/use, captured relation, imported demand, and physical/replay evidence; apply each actual first rejection to the unchanged original obligations without narrowing quantifiers. Keep `YulangClosure.SourceProblem.InferenceSoundness`, source Call/shared-witness, Generalize allocation, complete source/native correspondence, effect hygiene, principality, termination and production **OPEN** absent their separate governing proofs.

`DONE` requires exact-input authentication, pre-run ACCEPT, one bounded attempt, post-run review ACCEPT, complete row classifications and Luna integration. Any input/load/build/test failure is `CLOSED_INCOMPLETE`; no repair or retry. Parent and production gates remain OPEN.
