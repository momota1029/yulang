# Local-use FreshUse retention approval receipt

Date: 2026-10-17
Branch: `research/simple-sub-intrusion`
Approved proposal: `notes/design/2026-10-17-local-use-retention-code-contract.md`
Proposal SHA-256: `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a`
Exact review handoff SHA-256:
`tasks/agent-loop/inbox/20261017-local-use-retention-code-proposal-repair.md`
`e2a0f6afafbb74785d2d5c7bc16753cbbfb0a9ef6d2b01b6b37897e808331c4d`

## Decision

The user approved the reviewed option 1 with the message “採択で構いません”.
The decision covers the exact rows-preserving retention proposal above:
keep `LocalFreshRoute.rows` as its sole current owner and move the other eight
`FreshUse` maps once into a route-owned retained record. It also accepts the
proposal's stated resource tradeoff: retaining construction maps increases
session memory, may cause earlier resource-limit rejection, and has an
unmeasured practical envelope and overhead.

This authorizes a separate bounded compiler-code sprint for that single-file
representation change only. It does not authorize any language-semantic change,
new map consumer, version checker, semantic NPAIR evidence, expected-output
change, receive subtraction, or production promotion. Existing NPAIR and parent
gates remain open.

## Review and implementation pins

- Independent architect review: CLEAN, proposal readiness only; exact proposal
  and handoff hashes above.
- Independent spec review: CLEAN, proposal readiness only; exact proposal and
  handoff hashes above.
- Corrected M2 proof: `notes/theory/2026-10-17-local-use-existing-map-retention.md`,
  SHA-256 `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
- Compiler baseline commit: `9a2c7d80826ae33493f2bcc4786bc06e450ae36a`.
- `candidate_scheme.rs`: `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- `shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.

The source review is authorization to implement the reviewed representation;
it is not a runtime claim. The physical memory overhead and practical resource
acceptance remain unmeasured.
