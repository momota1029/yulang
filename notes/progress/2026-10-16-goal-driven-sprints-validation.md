# Goal-driven sprint implementation and verification receipt

Date: 2026-10-16
Branch: research/simple-sub-intrusion
Inspected source HEAD: 7336f290da53dc39cfc5be18dd492820d1b7451c
Source tree: 55314a43672c94da1b891ab9aa2209013ab2d394
Authority: user's explicit goal-driven sprint implementation request;
notes/design/2026-10-16-goal-driven-sprints.md
Status: implemented and deterministic checks passed; independent/live adoption
review NOT_RUN. No theorem, compiler behavior or model execution is certified.
Mode: M2 workflow/coordination change; zero executed reviewers (unavailable),
one fresh isolated spec_auditor required before live adoption. No architect
round was added because the user supplied the governing decisions.

## Actual changes

Replace per-packet dispatch with one fixed sprint contract and bounded autonomous
proof/implementation continuation. Add proactively assignable astra_prover and
preserve Luna/high implementation plus the separate frozen-handoff escalation.
Share Astra/resource quotas across roles and descendants. Keep original proof,
source/native, implementation and production gates distinct. A source-qualified
counterexample resolves a claim as REFUTED, never as a proved production premise.
Dependency revocation invalidates affected work/reviews, not unrelated lanes.

The root entry points and three active routing rules now explicitly select the
single sprint policy. Their former safety maps are copied byte-for-byte to
same-directory *.pre-sprint.md references using original Git blob IDs. Their
relative links and unrelated invariants remain intact. The three historical
2026-10-16 resident-loop decisions are not rewritten; exact supersession and
preserved scopes are declared in the new user-authorised decision.

Replace the oversized current board with a small navigation card and current.json.
Preserve its entire original blob at history/board-7336f290.md; preserve every old
inbox. New handoffs are per multi-stage assignment, not per lemma. The current
snapshot intentionally says RECONCILE, runtime UNAVAILABLE and no launched workers;
it explicitly does NOT assert that prior-session workers or leases disappeared.

Add a sprint skill, contract template, clearly non-executable Call/effects
candidate, stdlib-only offline model/checker, and transition regressions. No
actual daemon, automatic spawn, external process or network client is introduced.

## Deterministic checks actually executed

- `python -m unittest discover -s tools -p 'test_agent_sprint.py' -v`: 50 tests PASS.
- `python tools/agent_sprint.py simulate`: PASS; clearly labeled synthetic IDs,
  receipts and model observations. No actual agents or compiler execution.
- `python tools/agent_sprint.py check --inventory /mnt/data/source-inventory.json`:
  PASS on the connector-only changed-file snapshot. Five changed/new role TOMLs
  parsed; nine unchanged role paths checked against the fetched source tree
  inventory, NOT locally parsed. Config registrations, model floors, skill/UI
  metadata, policy entry points, compact state and candidate checked.
- `python -m py_compile tools/agent_sprint.py tools/test_agent_sprint.py`: PASS.
- Explicit changed-path/whitespace and size inspection: no compiler, production
  test, manifest/lockfile, question bundle or unrelated branch change included.

Regressions exercise concurrent lanes, internal successors retaining the goal,
blocked-proof/independent-code liveness, proactive and bounded Astra, global and
subtree quotas, exact exclusive leases, unchanged capacity retries, unsupported/
rate/auth failures, actual worker preservation on known routing mismatch,
requested-vs-observed UNKNOWN values, independent author exclusion and frozen
review hashes, major-review blocking, conditional/test non-closure, refutation
versus proof, dependency invalidation, STOP/end/restart with quarantined leases,
fresh resumption receipts without budget reset, descendant reconciliation,
idempotent handoff revisions, compact-state limits and the live adoption gate.

The model validates protocol structure only. It cannot authenticate a receipt,
judge mathematical truth/source adequacy, observe the actual effective model,
enforce OS file permissions, kill a worker or supply independent review.

## Integration and preserved scope

The editing environment could not clone GitHub directly (DNS unavailable).
Reads and publication use the connected GitHub interface. This is a partial
local snapshot, not an inspection of the user's live worktree or local index.
Byte-preserved archive mappings are in tasks/agent-loop/history/baseline-manifest.json.
Publication uses a coherent Git tree/commit based on the inspected remote HEAD,
then a non-forced expected-SHA update of the exact requested branch. A moved HEAD
must be inspected/reconciled rather than overwritten. The actual containing
commit and publication result are reported by the GitHub receipt, not invented
inside this immutable file.

Changed groups: AGENTS.md/override; active orchestration/budget/research rules
and preserved policy baselines; new sprint decision; two updated skills and one
new sprint skill with UI metadata; .codex config and five producer/dispatcher
roles; compact loop state/protocol/history and sprint templates; offline model
and tests; this receipt. No language or production inference delta.

## Remaining limits and exact next gate

Independent review: NOT_RUN; there is no available spawn/review interface here.
Live parallelism, Astra routing, STOP cancellation and runtime adoption: NOT_RUN.
Do not treat a configured model or a successful test as observed execution.
The pending review in current.json prevents ACTIVE adoption until a live Luna
primary records a fresh isolated review and reconciles every legacy worker,
descendant and outstanding lease. Resolve the candidate's exact original claims,
source owners, baseline hashes and exclusive outputs before granting it.

Cargo fmt/check/check-graph and compiler end-to-end suites: NOT_RUN. No compiler,
Cargo manifest, native semantics or production tests changed; this environment
has only the changed-file snapshot. Use ordinary existing compiler gates when
actual authorized compiler work is performed in its full checkout.

The unchanged nine specialist role contents and standalone Codex wrapper were
not runtime-tested. The inspected wrapper discovers .codex/agents/*.toml by
name/description, so the new role follows its existing registration convention;
this is a static compatibility observation, not proof of harness availability.

tasks/current.md, tasks/research-lab.md and notes/design/INDEX.md are intentionally
not appended or rewritten: this change supplies the direct active routing and
compact current-state receipt instead of duplicating the large historical logs.
Existing theorem/source status is preserved, and no parent gate is closed here.
