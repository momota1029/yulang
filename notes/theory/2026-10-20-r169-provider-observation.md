# R169 bounded ordinary-provider observation

Status: implementation result CLEAN-reviewed as a borrowed inspection view over existing retained candidate records. This is a solver inspection view over existing retained candidate records, not a constructor-event history, inference certificate, semantic consumer or sample-execution result.

## Surface and bounds

`CandidateInference::ordinary_provider_observation(max_rows)` scans the retained candidate graphs and selects ordinary `FunctionPort` records for `ArgumentEffect` and `ResultEffect`. For each parent relation `q`, it yields bounded borrowed rows for:

- the selected retained FunctionPort dependency;
- every retained dependency whose child is `q`, preserving the table's structural order;
- each retained bound admission whose relation is `q`;
- each existing physical emission whose admission names a `q` relation;
- every retained source `Origin` whose relation is `q`.

A row retains its graph index, the root FunctionPort ordinal it describes, relation ID, source-table ordinal and row kind, plus a borrowed `Debug` view of the exact record. No dependency is chosen by endpoint equality, count or a unique-route assumption. The public observation is a finite vector of references and row tags; it adds no state to a candidate graph. `max_rows` is clamped to 256 total rows, and `truncated()` reports when more eligible rows existed. The caller must treat truncated output as incomplete. Allocation failure and invalid candidate results fail closed as `ArtifactMismatch`.

`lambda_slot2_source_join()` explicitly reports `NotJoinedToContextRecord`: this observation does not itself join a context `Origin` or provider admission to a specific Lambda slot-2 source fact. Separate source-store provenance can identify exact source facts and their Causes; it does not make this context-local row view a historical typed-drain event log.

## Limits and evidence boundary

The dependency table preserves distinct structural Replay/Derived/Transport routes. It does not preserve every repeated constructor invocation: identical dependencies may be interned. Replay operation children and acknowledgements remain operation/index records and are not synthesized as a unique dependency event. The observation presents each retained structural record and relation-local evidence independently, preserving alternatives without asserting how one historical child index selected one dependency row.

Likewise, a `SourceOrigin` is the retained origin for the relation/drain; it is not by itself an owning Lambda constructor certificate. Source-store fact/provenance records retain the original source occurrences and exact Term pair separately. Connecting those source facts to the selected provider admission's own use maps and through Capture/shared anchors to its actual consumer remains the proof lane's open premise.

This code does not change relation generation, source facts, bound admission/emission, replay, rollback, solver state, candidate results or production APIs used for inference. The new method exposes research observations only. It does not enable the Yulang2 sample path and does not change any execution coverage.

## Verification status

Exact pre-edit source pins matched the reviewed R169 contract. Static review of the leased diff and call path only; no tests, builds, compiler/runtime execution, Yulang2/Yulang3 activity, external Oracle access or network use. Independent code review was CLEAN by `/root/r157_contract_review` on the exact leased source diff, including the `function_port_ordinal` grouping-field delta. Any inference that this observation proves the parent theorem is invalid.
