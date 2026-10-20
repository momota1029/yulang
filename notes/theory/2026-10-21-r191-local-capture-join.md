# R191 — local Capture/Replay source join audit

Status: **provisional source/native readback**. No proof, counterexample, or
production claim. Parent §§1, 6–7 and all A/B/source-native/production gates
remain OPEN.

## Exact current-worktree source and execution

The readback used the R187 bridge/relay source from its primary note:

```yu
act signal:
    our ping: () -> int
my finish (x:[signal] int) = x
my outer (t:[signal] int) = {
    my bridge (x:[signal] int) = outer x;
    my relay (u:[signal] int) = bridge u;
    catch t { signal::ping(), _ -> relay t, v -> finish t }
}
```

The HIR contained four authentic source Apply calls. `bridge u` is Apply
occurrence 13, callee Name occurrence 14, resolved local ordinal 0, level 2.
`relay t` is Apply occurrence 18, callee Name occurrence 19, resolved local
ordinal 1, level 1. No structural recovery occurred and candidate inference
completed on the current worktree.

Input source owners were frozen in R191's contract. In particular, the dirty
current `shadow_apply.rs` bytes matched their pinned SHA-256
`7c52bbd421de84d57efa7aba13a391b26eb4098a77199895482f720017be2fca` at probe
time. The ignored probe and full output were under `target/r191-readback/`;
driver SHA-256 `8e03d853c2197cb8fedb954422271a474b03238d339b11da1ddafb58f95ccf0c`,
output SHA-256 `5b722cb4cf6ec9fcd9fb374e06c75744b6fc677f426e9538a46b0702419892b8`.

## Exact local source and Replay observations

`CandidateSourceOccurrenceObservation` returned complete occurrence-selected
fact and origin lists for both Apply nodes. For `bridge u`, slot 0 was a direct
source drain, relation 58, with `ValueRow(13) <= NegativeFunction(Term 306)`.
The retained Replay dependency was child 59, lower parent 55, upper parent 58,
with ordered inputs:

```text
lower = ValueRow(13) positive <= PositiveFunction(Term 296)
upper = ValueRow(13) negative <= NegativeFunction(Term 306)
```

For `relay t`, slot 0 was a direct source drain, relation 95, with
`ValueRow(18) <= NegativeFunction(Term 338)`. Its retained Replay dependency
was child 96, lower parent 92, upper parent 95, with ordered inputs:

```text
lower = ValueRow(18) positive <= PositiveFunction(Term 324)
upper = ValueRow(18) negative <= NegativeFunction(Term 338)
```

Both ordinary-provider and source-occurrence views were untruncated for these
records. `ordinary_provider_observation` retained the exact local route for
`bridge u` as graph 0 / local route 0 / occurrence 14 / context use 1, and for
`relay t` as graph 0 / local route 1 / occurrence 19 / context use 2. This lets
the readback join the actual HIR local-callee occurrence, local identity,
retained local route and FreshUse map for these two calls. The bridge Capture
has two bounds (relations 45 and 19). The relay Capture has eight bounds
(relations 74, 60, 72, 73, 56, 57, 62 and 53), with 18 nodes and 9 rows.

## Exact boundary of the evidence

The higher-level `source_provider_observation` rejects both local calls with
`ArtifactMismatch`: its consumer requires `module_callee_target()`, while
`bridge` and `relay` resolve to local identities. The lower-level records can be
joined manually for this run, but they do not provide one typed, authenticated
local-provider consumer receipt. The retained Replay dependency exposes both
ordered inputs, yet it exposes no separate Replay-child completion receipt.
Every relay Capture snapshot has nonzero `EvidenceCoverage` gaps (56, except
relation 53 with 120). The full observer is not truncated, but these gaps still
prevent treating the retained snapshots as a complete emitted-fiber proof.

Therefore this readback authenticates the R187 candidate's local Apply-to-route
and ordered Replay rows, and repeats the same candidate missing-suffix table.
It does not certify absence of another authentic suffix, prove mapped-bound
admission under all required paths, or validate the finite interpretation
against every native relation. The local source/native parent remains open.

The next useful owner-local step is a local-callee version of the existing
source-provider join, including an actual Replay completion receipt and an
explicit completeness result for captured fibers. Such an observer can improve
evidence; it cannot itself prove the original theorem. No compiler code was
changed. The disposable probe is removed after closeout. Primary-only audit
charged 300s of a fresh 600s cap; 300s unspent, no carryover. No independent
review was available.
