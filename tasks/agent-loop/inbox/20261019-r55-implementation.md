# R55 Luna source-owner handoff

- Contract: `tasks/agent-loop/sprints/original-name-core-20261019-r55.md`, rev1.
- Source map: `notes/progress/2026-10-19-r55-original-name-owners.md`.
- Original-domain source entrance: `outer(q:[io]int) { forward(t:[io]int)=t; forward q }`; the call argument is the whole current formal Name and `forward` has the direct formal-Name body. Static resolved-carrier trace only; no parser/preflight/solve execution claim.
- Owners: source `FormalEntry` / `FormalNameEffect`; Lambda slot 4; Local and DefinitionUse incoming paths; Capture; one canonical FreshUse map; bound restoration; signed extrusion; qualified merge/replay; route rollback.
- Exact remaining owner judgment: prove original-domain event/source sets and signed representative histories preserve or recreate the same provider's mapped `e_t <= e_n <= e_R` route at every later real capture; direct-provider SCC alone does not exclude ancestor replay/merge.
- Implementation: **NO_SAFE_CODE_SLICE** under read-only source lease. No tests, builds, code, runtime, probes or measurements.
- Parent remains OPEN 0→0; quantifiers/domain/expected outputs/A-B unchanged; R50 NOT ADOPTED.
