# R202–R212 compact audit archive

This receipt consolidates the resolved lineage and Capture-frontier audit milestones. Full notes and sprint contracts remain in the repository; their individual pins are retained below. R213 applies their evidence to the original open R183 gate.

| Sprint | Outcome note | Note SHA-256 | Contract | Contract SHA-256 | Charged seconds |
|---|---|---|---|---|---:|
| R202 | `notes/theory/2026-10-21-r202-capture-fiber-lineage.md` | `503ad8116dbad06968cc7208f633332c9d1d1cf65e7c7139cdbe8080159c5adc` | `see note` | `recorded in note/contract` | 60 |
| R203 | `notes/theory/2026-10-21-r203-capture-fiber-lineage.md` | `574bc557e2c2ad27e3e8a4d35517b1be385872e563e53592dbf6d646eb147279` | `see note` | `recorded in note/contract` | 32 |
| R204 | `notes/theory/2026-10-21-r204-coverage-gap-semantics.md` | `23037d7cc7edecdb633a75d64b9a2ef7de38f3aaee68592d8362bc3cf12085f8` | `tasks/agent-loop/sprints/coverage-gap-semantics-20261021-r204.md` | `recorded in note/contract` | 35 |
| R205 | `notes/theory/2026-10-21-r205-source-origin-capture-history.md` | `2cf6e38ebb176271eefb7910e4c1a061e3d53cdbe8b545737f964740e1c84225` | `tasks/agent-loop/sprints/source-origin-capture-history-readback-20261021-r205.md` | `recorded in note/contract` | 35 |
| R206 | `notes/theory/2026-10-21-r206-source-origin-completion.md` | `191cee7afd6a1a8eed4bf0a4e5d352946a6e2aaf6556cfc8ac2f48eabc18ba81` | `tasks/agent-loop/sprints/source-origin-completion-and-expression-join-20261021-r206.md` | `recorded in note/contract` | 40 |
| R207 | `notes/theory/2026-10-21-r207-capture-origin-slot-join.md` | `9faa7fe0d389fa52f566beb1f5d8afe191095091edf71bd9bdb43be73ff3b198` | `tasks/agent-loop/sprints/all-capture-origin-slot-join-20261021-r207.md` | `recorded in note/contract` | 40 |
| R208 | `notes/theory/2026-10-21-r208-lambda-slot4-owner.md` | `890a2fe910236e3a7a3f30611d603137375d04733e9f72df27c7a4d65ea68680` | `tasks/agent-loop/sprints/lambda-slot4-owner-and-capture-membership-20261021-r208.md` | `recorded in note/contract` | 35 |
| R209 | `notes/theory/2026-10-21-r209-callee-binding-frontier-join.md` | `2b827f101b3dd2f3fe7a026b116f1e6b94d4a9913a70e4a21b986871067fd8b9` | `tasks/agent-loop/sprints/callee-binding-lambda-frontier-join-20261021-r209.md` | `recorded in note/contract` | 45 |
| R210 | `notes/theory/2026-10-21-r210-provider-row-map-frontier-path.md` | `8a2854323bb73a2de1bb81a37e505f0019d78811b976ea8f3246cb32ef9f77ed` | `tasks/agent-loop/sprints/provider-row-map-and-frontier-path-20261021-r210.md` | `recorded in note/contract` | 50 |
| R211 | `notes/theory/2026-10-21-r211-source-owner-alias-search.md` | `59a4a856dd8ead423843bf94a9d0bfe5b05c4f92d3847eae4645264926fa6a5f` | `tasks/agent-loop/sprints/source-owner-alias-and-mapped-bound-search-20261021-r211.md` | `recorded in note/contract` | 20 |

| R212 | `notes/theory/2026-10-21-r212-source-owner-alias-readback.md` | `8b753156953d9c048d512b9a415a5aaa5cbb01a2d133c9a5f59d3f7464cac604` | `tasks/agent-loop/sprints/test-only-component-kind-path-fix-20261021-r212.md` | `0fb6383bf5755c38e5c7082fe7bc920f9c905193745f54d0d3397bdfe41bc5ce` | 40 |

## Integrated finding

R202–R204 joined physical Capture rows and decoded observer coverage. R205–R207 found completed source Origins on captured Name slots 1/2. R208–R210 joined relay Lambda slot 4 and its local callee route, showing source bound Effect(10) ≤ Effect(31) outside the Capture graph while local Effect(31) maps to Effect(32). R211 first validation stopped at a private test import. R212 corrected only the test path, confirmed `rep(Effect(10)) = Effect(10)`, and enumerated the entire route effect-bound graph with no Effect(10) edge or bound to Effect(32). The resulting source-qualified candidate witness is recorded at `notes/theory/2026-10-21-r213-source-qualified-capture-frontier-witness.md`.

These are candidate-solver observations for one fixture. The native theorem and production gates remain open pending fresh independent review and Luna adjudication.
