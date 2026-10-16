# Local-use retention proposal handoff

Sprint-ID / contract revision and SHA-256:
`local-use-existing-map-retention-20261017`, revision 3;
`be13224abe1dcfbcbc9e1c9eea8bfb83e9b2192854e8bdfb9e28ba4ed584e049`.

Assignment-ID / handoff revision:
`LOCAL-MAP-RETENTION-PROPOSAL-20261017`, revision 1.

Parent gate / original theorem:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN; accepted domain and
quantifiers unchanged. The parent locator and source route are pinned in the
sprint contract and corrected proof.

Baseline / direct dependencies:

- `crates/yu-solver/src/candidate_scheme.rs`:
  `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- Corrected proof:
  `notes/theory/2026-10-17-local-use-existing-map-retention.md`,
  `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
- Repair handoff:
  `tasks/agent-loop/inbox/20261017-local-use-map-version-repair.md`,
  `2d3ca0ff0115f4098dd763b8c9ec3d8468d00c47007f51cca66d93bbad0218e2`.
- R1:
  `notes/theory/2026-10-17-npair-use-certificate-retention.md`,
  `c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`.

Role / worker / session / launch:
Luna primary and sole author/integrator; current session. Proposal packet was
acknowledged after the fresh M2 compiler_referee delta review completed CLEAN.
No descendant.

Requested/effective model and effort:
Not separately exposed for the primary; effective metadata UNKNOWN.

Exact write paths:

- `notes/design/2026-10-17-local-use-retention-code-contract.md`
- `tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal.md`

Outcome class:
Unapplied implementation proposal. No compiler code was written.

Outcome and source-to-native path:
The proposed change moves the existing `FreshUse` into `LocalFreshRoute` at
the already-successful `commit_local_use` boundary and updates retained-byte
census to count the moved maps. The path is constructor maps → local fresh-use
restoration → final route reservation → transaction success → committed local
route. Failed attempts remain private and are truncated/restored by the existing
route journal. The proposal intentionally supplies no source constraints,
propagation derivation, At, consumer selection or subtraction.

Parent application / remaining premises:
The corrected conditional M2 says that registered queries evaluated validly
at the pinned precommit version `v0` return the same answer. Invalid or changed
projections carry no equality claim. This retention proposal does not prove
that native referents stay alive, IDs are not reused, addresses survive
relocation, or historical `v0` checking exists. Those owners and a later
consumer/invalidation API remain open. Whole native `rho_u`, source/native
adequacy, parent and production remain OPEN.

Alternatives and requested user decision:
Option 1 moves all existing `FreshUse` maps into `LocalFreshRoute` (proposed,
smallest source delta). Option 2 builds a compact query projection (smaller
retained memory but needs a query type and a new completeness proof). Option 3
adds a session-owned semantic Use ledger (broader, but the current producers
lack descriptor/provider/At/future evidence). The user must approve the exact
selected option after independent architect and spec review; no code authority
is inferred from adoption of the sprint or proof.

Independent review:
Correction proof M2 received CLEAN delta review only. The code proposal has
not yet received its required independent architect or spec review. These are
the next sequential review lanes, each under the existing 120-second cap.

Checks and exclusions:
Read-only inspection of exact source owners and direct SHA-256 pins; static
`python3 tools/agent_sprint.py check` passed for current sprint state. No tests,
probes, builds, Cargo or compiler execution. No semantic/expected-output edits.

Resource charge:
The existing Luna proposal-author cap is 600 seconds; this stage is frozen
within that cap. No carryover or expansion requested.

Next step / stop:
Luna freezes exact artifact and handoff hashes, then assigns architect review
and, after that reviewer STOPs, spec-auditor review. No compiler edits before
both reviews and explicit user approval.

Mutual TODO:
`LOCAL-MAP-RETENTION-PROPOSAL-20261017` — architect and spec reviewers judge
the exact `FreshUse` move, accounting, rollback and semantic boundary against
the pinned proof and source. Falsifiers include any missed capacity charge,
failed-transaction partial retention, invalid-v0 equality claim, or inference of
NPAIR authentication from map presence alone.

Worker state:
Luna's proposal author stage STOPPED; both exact output files frozen. No
descendants or remaining author steps. Parent remains OPEN.
