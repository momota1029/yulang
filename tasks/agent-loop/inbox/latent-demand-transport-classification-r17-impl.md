# R17 implementation handoff — per-row authentication events

Status: **FROZEN / STOP**

## Authority and exact inputs

- Contract: `tasks/agent-loop/sprints/latent-demand-transport-classification-20261028-r17.md`
  - SHA-256: `19896d719176b6ffb84a4a1d51b03672246398c07539d4ffc8f80c14b879f53d`
- Input manifest: `tasks/agent-loop/sprints/latent-demand-transport-classification-20261028-r17-inputs.json`
  - SHA-256: `5ff66c9237154d5d15161d68871c06b94d1de3e935edc838f4781f5758a3c121`
- Sole source path changed: `isolated/latent-demand-transport-classification-r17/crates/yu-solver/src/candidate_scheme.rs`
  - SHA-256 after change: `f0f8c15a78620ff34c85433fefbf842f4b716831207057a1804e7a27f2f77a3d`

## End-to-end behavior contributed

The existing per-row `replay_rows` loop now calls `authenticate_demand_transport_observed` for each row that passes its pre-existing native-call and port guards. It passes the same context, replay row, native demand, `ports` function, and `None` override as the former silent wrapper. The same returned `Option<DemandTransportEvidence>` feeds the unchanged `emission_cases` collection.

For every observer event emitted by the existing authentication core, the test log now includes call, FreshUse identity, child/lower/upper relation IDs, demand root, owner, route index, and stage. No authentication guard, route selection, evidence construction, expected output, source fixture, or production code changed.

## Parent/source/native correspondence and boundaries

This is instrumentation only. It correlates each visited replay row with the row's captured native demand and retained route authentication events. It does not establish source occurrence to Call/use correspondence, source adequacy, a native theorem, or completeness of the source-to-native map. R16 evidence reused as context was the four same-invocation root joins and `session.execute() == Ok`; R16's emission evidence vector was empty. The prior call-only selection was unsuitable for this fixture because call 0 has two replay rows (uses 1 and 3). This loop now preserves and visits row identity instead of treating call identity as unique.

The original source soundness, Call/shared-witness, Generalize allocation, complete source/native correspondence, effect hygiene, principality, termination, and production obligations remain OPEN. This bounded finite-fixture trace cannot establish a general defect or authorize repair. Existing guards still skip a row if its native call or copied ports are absent; the existing observer emits events only where the authentication core reaches an observer call. Those cases may need explicit classification at the primary/source evidence layer, but I did not change guard or observer semantics under this lease. `EvidenceCoverage { gaps: 56 }` is unchanged by this source delta.

## Exact diff

At the existing loop around `candidate_scheme.rs:8418`, replace the `authenticate_demand_transport(...)` wrapper call with:

```rust
let evidence = state.authenticate_demand_transport_observed(
    context, replay_row, native.demand, ports, None,
    |owner, route, stage| eprintln!(
        "ReplayAuthenticationClassification call={} use={} child_relation={:?} lower_relation={:?} upper_relation={:?} root={:?} owner={owner:?} route={route} stage={stage:?}",
        replay_row.call, replay_row.demand.use_instance,
        replay_row.child, replay_row.lower, replay_row.upper,
        replay_row.demand.root,
    ),
);
if let Some(evidence) = evidence {
```

The surrounding insertion into `emission_cases` is unchanged. Exact source delta is one hunk in the sole leased source file; no other path was written.

## Checks, budgets, and scratch

- Contract and manifest hashes rechecked against the admitted values.
- Reviewed the existing observed function signature and `ReplayDemandRow` fields against the source to ensure the closure uses existing IDs and the same arguments. This was a manual source check only.
- No Cargo/build/test, formatter, checker, Git mutation, or other validation command was run, per contract.
- Requested role/model and effort: pinned Luna/high implementer. Observed runtime model metadata was not exposed in the execution interface; no fallback or in-place model change occurred.
- Grant: 300 seconds maximum; this handoff freezes the work before that bound. The terminal did not expose per-agent CPU accounting. Luna should record the authoritative live runtime/budget receipt.
- New path: this exact handoff file. Scratch paths: none.

## Review status and next in-envelope step

Implementation is frozen and awaits independent review. The next authorized step is fresh review of the exact source diff and the existing R17 input closure; execution remains gated on reviewer ACCEPT and Luna's contracted single Cargo attempt. This handoff is not independent certification.
