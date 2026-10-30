# EFFECT-PERMISSION-MODULE-USE / R40 READ2

Status: primary-admitted, read-only bounded source packet. It authorizes no
compiler edit, proof edit, build, test, environment, cache or source promotion.

## Objective

Determine whether an existing construction retains the mapping from an
original computation-formal registration's argument-effect port to the
argument-effect port instantiated for one exact module use. If it does not,
name the first missing provenance constructor. Do not implement a consumer.

## Baseline and inputs

- Git baseline: `720eacd38118a1fb408c5886525f3af241f5307d`.
- Prior intake: `tasks/agent-loop/history/effect-permission-module-use-20261031-r40-preflight-intake-r1.md`, SHA-256 `4708b9de84447800e8f1c0851b76fe511ed82e78a1804a58d9cab2d5be592d48`.
- Read-only source file: `crates/yu-solver/src/candidate_scheme.rs`, SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.

Exact permitted function bodies in that file:

| Function | Lines | SHA-256 |
|---|---:|---|
| `freshen_candidate_graph_retained` | 4242–4258 | `6605d0d4c346af9f274d9d8c07256a5e77690886ad942c30f19f75923f9f1e1a` |
| `freshen_candidate_graph_core` | 4260–4280 | `5920a3b8c85d3e37f9c1c4af1c46f11b491f3d46a0acef195101dbc70ae4018d` |
| `prepare_candidate_fresh_use` | 4281–4668 | `d0d7994e00e877d39e1da3f610b4209614bb39788181cafd1d7b42c393666584` |
| `begin_candidate_fresh_bound` (restored-bound provenance only) | 4669–4716 | `f3752551c4cdc01e2529c4aed22932467e189b0e74c84a99bd772d0aa58f0c7a` |
| `instantiate_candidate_graph` | 4717–4800 | `c3c628ace48cc3c5e7c4a93314f86f3a5a6b80c394999ea6b12a6071028d40bd` |

No other source path or body is authorized. In particular, do not inspect
`shadow_apply.rs` or broaden into whole-file search. The prior R40 reader's
240-second allowance is fully consumed; this packet has its own 600-second
cap, with reader ≤300 seconds, primary intake/adjudication ≤150 seconds, and
independent source validation reserve ≤150 seconds. No carryover is available.

## Required trace and falsifier

Trace the actual FreshUse term/row mapping, exact module-use identity, and
Function argument-effect child. Distinguish reconstructed terms from retained
source certificates. Establish whether the original registration-to-instanced
port mapping is tied to this exact use, rather than inferred from shared row,
tail or family equality.

Falsifier: distinct registration-specific permissions sharing `e` become
interchangeable, or the alleged argument-effect mapping cannot be attributed
to this exact source use. Preserve the `{signal | e}` / `{write | e}` witness.

## Output and review

The sole reader write is
`tasks/agent-loop/inbox/effect-permission-module-use-r40-read2.md`.
Report source coordinates, constructors, mapping direction, provenance
retention, exact hashes, falsifier result, and any first absent constructor.
No source writes. After the reader stops, an independent read-only source
validation checks the frozen report within the reserved 150 seconds. Only Luna
may admit later implementation after adjudicating that review.
