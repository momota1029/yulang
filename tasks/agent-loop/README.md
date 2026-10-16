# Sprint state and assignment handoff protocol

Authority: [goal-driven-sprints.md](../../rules/goal-driven-sprints.md).
This directory records scheduling evidence, not language meaning or theorem
status. The new primary-owned snapshot supersedes the old dispatcher-owned
append-only board after an acknowledged live writer reconciliation.

## Read and write ownership

Read current.json, the selected sprint contract and exact needed source locators.
Read historical task/proof records only when a claim/owner requires them. Luna
owns current.json and Git. A dispatcher normally returns a proposed delta; one
explicit recorder lease is possible, never concurrent central writers. board.md
is a small navigation card. Old board/inbox history is preserved without loading
it all on startup. The baseline manifest records byte-preserved Git blobs.

An assignment gets exact artifact and one exact handoff/inbox file lease for its
whole multi-stage envelope. No directory-wide/wildcard lease or one-file-per-lemma
rule. Workers never write another inbox or the central state. Existing inboxes
remain valid immutable evidence; no migration rewrites their contents.

## Frozen assignment handoff

Use this compact content in the one assigned file, or return equivalent fields
in a message when file writes are unavailable:

```text
Sprint-ID / contract revision and SHA-256:
Assignment-ID / handoff revision (positive integer):
Parent gate / original theorem and scope locator:
Baseline / direct dependency hashes:
Role / actual worker ID / current session / launch or resume receipt:
Requested model and effort / observed model and effort (UNKNOWN if absent):
Exact leased paths / all authors and contributing descendants:
Outcome class: candidate | conditional | proof | source-qualified-counterexample
               | source-native-evidence | implementation | provisional | probe
Parent application: what follows now; exact remaining premise and owner:
Source constructors -> generated constraints -> propagation -> consumer/native path:
Artifact locators and byte hashes / frozen review snapshot:
Checks, coverage, omitted cases and resource budget spent/remaining:
Next related step inside the existing envelope, or exact boundary needing Luna:
Mutual TODOs: stable request IDs, original parent, first missing evidence,
             source owner, required inputs, proposed outputs and falsifier:
Worker state / writes stopped receipt / unresolved descendant leases:
Commit-ready milestone or explicit pending review/integration:
```

Freeze the submitted revision and send its ID/revision/SHA-256. Luna may
acknowledge intake directly; no mandatory dispatcher round. Identical ID/revision/
hash is idempotent. Changed content requires a new sequential revision after
acknowledgement; a changed same-revision hash is a conflict. Keep prior frozen
receipts or immutable snapshots. The offline model hashes canonical JSON fixture
payloads; real Markdown/artifact receipts hash actual frozen bytes.

A TODO requests evidence; it is not permission to write another lane's files,
spend more resources, alter semantics or close its parent. Cross-lane dependency
changes return through Luna. Autonomous continuation means related in-scope work
under existing exact leases, not autonomous ownership or authority expansion.

## Separate task, worker, review and parent status

Tasks may be PROPOSED/READY/ASSIGNED/RUNNING/RESULT/REVIEW/DONE, with explicit
BLOCKED/CANCELLED/FAILED/STALE alternatives. A multi-stage RESULT is not DONE.
Worker observations are NOT_STARTED/RUNNING/WAITING/BLOCKED/STOPPED/UNKNOWN.
A resident idle identity is WAITING. RUNNING requires a current-session actual
launch/resume and active-work receipt, not a configured role or old worker ID.
Known routing mismatch keeps the real returned identity and quarantined lease;
it is not a nonexistent launch and cannot justify overlapping replacement.

A REVIEW target is frozen, not approved. DONE requires the necessary fresh
independent review plus Luna's integration receipt. Mathematical, source/native,
implementation and production parents are separate and never auto-close from
packet completion, test counts or a conditional lemma. REFUTED is distinct from
PROVED and cannot satisfy a production prerequisite; revoking a proved premise
invalidates its dependent work and reviews, not unrelated lanes. A coauthor or a worker
that supplied the proof's counterexample/repair cannot independently review it.

Lease states are HELD, FROZEN or QUARANTINED. A frozen artifact cannot change under
a review of those bytes. A stopped-writing receipt permits a primary-directed
handoff only after all descendants and generated outputs are accounted for.
An unknown writer retains its paths and resource reservation. Timeouts, a new
board, STOP or session end do not themselves prove cessation.

## STOP, restart and compact history

STOP is immediate and independent of dispatcher availability. Use actual runtime
cancellation tools when supported. Clear stale RUNNING observations on pause/end;
without write-cessation evidence record UNKNOWN and quarantine leases, not
STOPPED. Preserve actual worker IDs, model observations, pending reviews,
authorship, spent budget and exact resumption conditions.

Resume with fresh session/active-work receipts and revalidated dependencies.
Do not reset spent sprint/Astra budgets, resurrect old RUNNING states or take
unknown leases. Reconcile legacy workers before activating this migration seed.
No live tool support means explicit degraded serial work, not a fictional team.

Keep current.json <=16 KiB with at most 32 pending items. At a substantial
milestone freeze a uniquely named outcome receipt, verify its content hash and
history locator, then remove only resolved entries from current state. Never
remove active/unknown leases, pending reviews or unconsumed results to shrink it.
Stop admissions if they cannot fit. The archive records original goals, before/
after evidence, remaining premises, substantive implementation behavior, review,
checks, Git outcome and limitations. Avoid duplicate micro-progress narratives
in tasks/current.md, tasks/research-lab.md and the historical board.

## Offline verification and its boundary

```sh
python tools/agent_sprint.py check
python -m unittest discover -s tools -p 'test_agent_sprint.py'
python tools/agent_sprint.py simulate
```

No command spawns a worker, writes repository state, runs a compiler or contacts
a network. `check --inventory FILE` explicitly supports a connector-only partial
snapshot: unchanged roles listed there receive existence/SHA-inventory checks,
not local parsing; the output identifies that limitation. Use plain `check` in
a full checkout. Simulated IDs and receipts are test fixtures, not live evidence.
The model is not a full scheduler, runtime authenticator, OS lease enforcer,
mathematical checker or independent reviewer. The live primary still owns those
judgments and must reconcile actual acknowledgements before any action.

## One-time migration review gate

The checked-in migration snapshot records INDEPENDENT-REVIEW as NOT_RUN.
Before live adoption of this policy/tooling revision, Luna must obtain a fresh
isolated review of the frozen diff, adjudicate findings and record its receipt.
Keep the snapshot in RECONCILE until both that review and legacy-worker/lease
reconciliation finish. Static tests and the editing primary's reread do not lift
this gate. This is one adoption boundary, not a new per-step review ritual.
