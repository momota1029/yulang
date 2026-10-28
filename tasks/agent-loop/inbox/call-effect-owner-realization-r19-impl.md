# R19 implementation handoff — typed same-route Function selection

Status: **FROZEN / STOPPED; pre-run review pending**

## Assignment and frozen inputs

- Sprint: `CALL-EFFECT-OWNER-REALIZATION/20261028-r19`, revision 2.
- Contract SHA-256: `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`.
- Input manifest SHA-256: `f287059a08410cf644644be214ba622de92d3e2d10c4897441cbb360c91ca22d`.
- Rust base: frozen R18 candidate copied into the R19 isolated snapshot.
- Exact assigned Rust paths:

| Path | SHA-256 |
|---|---|
| `isolated/call-effect-owner-realization-r19/rust/crates/yu-solver/src/candidate_effect.rs` | `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b` |
| `isolated/call-effect-owner-realization-r19/rust/crates/yu-solver/src/candidate_context.rs` | `be1be2277d54288ba4ae542e003dabc294031c29cb26b2b5d0454b0d1c102bd0` |
| `isolated/call-effect-owner-realization-r19/rust/crates/yu-solver/src/candidate_scheme.rs` | `985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c` |

Only `candidate_scheme.rs` changed in this assignment. The R19 diff against the frozen R18 candidate is one hunk at the same-route Function selection boundary.

## Change and source correspondence

The previous selector compared only the retained term and returned one undifferentiated `None` for either zero or multiple matches. The replacement scans only the already selected FreshUse route, maps each candidate through `mapped_endpoint_at(graph, mapped_rows, retained, node)`, and requires equality with the complete typed endpoint in the Replay lower/upper `BoundKey`. This uses the route's row map, retained term/effect maps and Function polarity. It classifies zero, exactly one and multiple matches separately for positive producer and negative consumer nodes. Exactly one of each continues to the existing four typed-port checks; zero or multiple fails closed with a distinct rejection stage.

Route traversal, the Replay fixture, authentication guards, typed port equations, callback order and returned `Option<DemandTransportEvidence>` are unchanged. No production path, inference choice, expected output, fixture, dependency or language meaning changed. The four R18 replay rows remain the bounded execution probe; none is yet authenticated by this edit alone.

## Verification and limits

- Static source inspection only; no formatter, build, Cargo, test or Lean command was run.
- The source lane authenticated 726 of 727 current R19 inputs and stopped before source-body reads: the pinned baseline for this file was `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`; the primary-edited candidate was `985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c`. All 11 parent pins matched. This was a primary sequencing error; its frozen STOP receipt is `tasks/agent-loop/inbox/call-effect-owner-realization-r19-source.md` (SHA-256 `5708927ca95ab623979d3580704bd0b2be13a13fda07c324b74c45971252dd4c`).
- The contract permits one focused Cargo attempt only after a fresh independent pre-run review ACCEPT and sufficient primary budget. The remaining primary closeout reserve is not authenticated, so no Cargo attempt will be made in this revision.
- This edit distinguishes route-local typed match cardinality; it does not itself establish any missing constructor-to-consumer equation, source/native correspondence, original `InferenceSoundness`, effect hygiene or production correctness.
- Astra's frozen proof handoff independently identifies the absent positive Function ownership and four typed port equations as unsupplied premises. The Lean lane found no supported original theorem type and delivered no module.
- Parent, native, effect-hygiene and production gates remain **OPEN**.

Writer STOPPED after freezing these paths. No descendants, Git, build, Cargo, tests or Lean execution occurred in this lane.
