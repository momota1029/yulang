# Resident-loop TODO exchange

Contract: [2026-10-16 workflow decision](../../notes/design/2026-10-16-resident-research-loop.md).
This directory stores scheduling and handoff state, not theorem authority.
`tasks/current.md`, governing sources and adjudicated proof records retain their
meaning. A task request cannot close a proof or authorize new semantics.

## Ownership

Luna leases `board.md` exclusively to the resident `next_action_selector`.
Only that dispatcher writes it until an acknowledged freeze/handoff. Luna reads
frozen board revisions, sends receipts and owns all actual dispatch and Git.

Each producer packet receives a unique exact path such as
`tasks/agent-loop/inbox/sessionA-impl-001.md` or
`tasks/agent-loop/inbox/sessionA-proof-001.md`. These are format examples, not
current leases or running workers. Allocate the actual session/packet ID before
dispatch. Both roles may submit multiple TODOs in their own assigned file; no
worker edits another inbox, and no wildcard write permission is implied. The
one-file-per-packet pattern also works for bounded proof leaves when Luna has
preallocated their exact inbox leases.

A producer freezes its submitted revision and sends IDs plus its SHA-256 hash to
Luna; Luna forwards that immutable snapshot/locator to the dispatcher. Intake
acknowledgement records each ID/hash and canonical task ID. Only then may the
producer append a new revision; preserve previously acknowledged content. Intake
is idempotent for an identical ID/hash. A changed hash needs a new revision and
acknowledgement, not a silent replacement. A worker unable to write its inbox
returns the same fields in a message for Luna to relay; only the dispatcher
writes the central board. Never read a producer's half-written submission.

## TODO template (one block per request)

```text
Request-ID: <session-packet-sequence, stable and unique>
Revision: <positive integer>
From: <implementer|prover|next_action_selector; actual worker ID or unknown>
To: <implementer|prover>
Parent-gate: <original gate ID and exact authoritative locator>
Baseline: <commit SHA plus hashes of relevant uncommitted/frozen inputs>
Kind: <proof|implementation|source-evidence|review-request|decision-request>
Claim/task: <concrete construction or original theorem with quantifiers>
Missing-evidence: <first missing premise and why it matters>
Owners: <actual constructor/consumer paths and symbols>
Depends-on: <canonical task IDs or none; necessary vs optional>
Scope: <approved scope, exclusions, any explicit provisional boundary>
Acceptance: <observable artifact/evidence and falsifier; tests are not proofs>
Proposed-outputs: <exact paths; proposals, not leases>
Checks/resources: <verification owner, bounded commands/CPU/process/time>
Priority-reason: <what this unblocks; next implementation benefit>
Stop/escalate: <specific obstruction/budget and evidence needed for Astra>
```

Deduplicate by original parent, scope/quantifiers, missing evidence and owning
construction; retain request aliases and distinguish materially different claims.
The dispatcher may originate tasks from inspected progress. Producers can request
either role, but neither assigns work directly to the other.

## Board and transitions

Keep one compact current board: session/provenance, the three role states,
canonical task rows, recent intake receipts and the latest action decision.
Detailed derivations stay in existing research artifacts. Each task row includes
ID, original gate/locator, target, state, real dependencies, frozen input/output
locators, acceptance evidence and next action. Put long packet details in the
linked frozen inbox or primary dispatch packet rather than growing a second log.

Task states: PROPOSED -> READY -> ASSIGNED -> RUNNING -> REVIEW -> DONE.
BLOCKED and CANCELLED are explicit alternatives; a justified task needing no
review still needs Luna's integration/completion receipt before DONE. READY
requires authority and established required inputs. ASSIGNED is a selected packet
with no confirmed execution yet. RUNNING requires a real launch/resume receipt
for that packet, not merely a retained worker ID. REVIEW means the producer froze
its artifact, not that a reviewer has passed it. DONE records the required
independent review and Luna integration receipt, never a producer's self-report.
Parent theorem/source/implementation/production gates stay separate.

Worker states: NOT-STARTED, RUNNING, WAITING, BLOCKED, STOPPED, UNKNOWN.
A worker may stay resident in WAITING after its packet returns. Record requested
and observed model/effort separately; unreported actual settings are unknown.
A restart requires runtime reconciliation, not copying old RUNNING states.

Every decision considers both lanes. Ready authorized implementation plus an idle
implementer must produce an implementation packet; ready independent proof runs
alongside it. A genuine dependency cycle gets a minimal evidence/construction
route or exact blocker, not indefinite mutual waiting. Freeze the board and all
included artifacts for Luna's coherent checkpoint; pending question bundles and
unrelated files remain excluded.
