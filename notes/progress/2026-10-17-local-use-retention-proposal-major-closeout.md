# Local-use retention proposal sprint closeout

Sprint: `local-use-existing-map-retention-20261017`, contract revision 3,
SHA-256 `be13224abe1dcfbcbc9e1c9eea8bfb83e9b2192854e8bdfb9e28ba4ed584e049`.
Outcome: **PARTIAL — proof M2 CLEAN; implementation proposal MAJOR**.

## Completed evidence

The corrected conditional M2 proof pins precommit version `v0` and claims
answer equality only for valid same-version evaluations. Invalidated or
unavailable projections carry no equality claim. A fresh compiler_referee
delta review was CLEAN within this corrected M2 scope. Exact proof hash:
`f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
Correction handoff hash:
`2d3ca0ff0115f4098dd763b8c9ec3d8468d00c47007f51cca66d93bbad0218e2`.

Luna froze an unapplied single-file proposal to move all of `FreshUse` into
`LocalFreshRoute`. Independent architect review found a MAJOR source
applicability defect: `shadow_apply.rs::fresh_use` and existing tests read
`LocalFreshRoute.rows`; removing it breaks those consumers. `FreshUse.rows` is
private across modules, so redirecting the sibling consumer requires an access
decision. The review also found that keeping every map increases session memory
and may cause earlier resource-limit rejection; practical overhead is
unmeasured. The exact rejected proposal remains immutable at:

- `tasks/agent-loop/snapshots/20261017-local-use-retention-proposal-pre-repair.md`,
  SHA-256 `a346ef6812109eb181cf160127959ac8320389b1a8a2d52e566464039601fb55`.
- `tasks/agent-loop/snapshots/20261017-local-use-retention-proposal-handoff-pre-repair.md`,
  SHA-256 `572e06a32b268dc3d089c5b4d27b4361fa194ca133857dc6bb2da8c7edec14ad`.

The proof's broader parent, whole native `rho_u`, source/native adequacy,
consumer, and production remain OPEN. No compiler source, tests, fixtures or
expected outputs changed. The static `agent_sprint.py check` passed; no tests,
builds, probes or compiler executions ran.

## Resources and Git

Charged: proof authors 420s, proof reviews 180s, proposal author 600s and
architect review 120s = 1320s. The remaining spec 120s and coordination 120s
were retired at sprint close; they were not reassigned as repair time. The
following commits were pushed without force:

- `f4cb9b138` — corrected M2 and frozen handoff/state.
- `14f17e991` — unapplied retention proposal and handoff.
- `c9993c2b3` — recorded the MAJOR review blocker.

The foreign dirty file `tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`,
three historical UNKNOWN reservations and quarantined board lease remain
untouched.

## Successor

The selector recommends a new 360s correction sprint. Preserve the existing
`LocalFreshRoute.rows` owner and all current consumers. Move every other
`FreshUse` allocation exactly once into a separate owned record, and count
every retained allocation/header exactly once. State plainly that increased
session memory may cause earlier resource-limit rejection; practical overhead
and the unchanged resource-acceptance envelope are unmeasured. The new sprint is
proposal-only. CLEAN reviews and explicit user approval remain required before
any compiler edit.
