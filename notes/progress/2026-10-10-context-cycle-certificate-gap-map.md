# Context cycle certificate lifecycle gap map

Status: read-only implementation audit plus conditional lifecycle witnesses;
the approved two-cycle implementation gate remains open.

Baseline: `77e723cdb7ef28c43033b6f8dd2c866154a457a6` on
`research/simple-sub-intrusion`.

Authority: [contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§4–7. This audit does not reopen or extend the selected gate.

## Current owners and missing lifecycle

| Concern | Current owner/evidence | Missing for the approved gate |
| --- | --- | --- |
| Inferred-entry origin | `lib.rs::admit_lambda_fact` creates fresh entry and returned Effect rows and the source-owned slot-3 entry-to-return and slot-4 body-to-return constraints. | No retained evidence distinguishes the inferred-entry flow from a written formal interface. |
| Entry authorization | `candidate_context::EntryCertificateId` and `ContextExpr::BothFromRight` exist as opaque structural tokens. | No authentic minting owner, retained certificate record, or production authorization consumer. Freshening rejects certificate-bearing contexts. |
| SCC identity | `candidate_intrusion::settle_candidate_intrusion` and `Dependencies::components` derive endpoint/bound/Function-port SCCs for recorded parent-copy equality. `generation` advances after a real merge. | This generation represents equality-set changes, not the selected symbolic PUSH or POP/PUSH circuit certificate, its exact count relation, or dependencies. |
| Relation operations | `candidate_context::State` retains exact `(TypedPairKey, ContextId)` relations, ordered Replay derivations, fibers, and provenance. | Production execution accepts identity and a closed filter prefix. Nonempty source operations, contextual Function transforms, and the two exact circuit recognizers are absent. |
| Late dependency changes | Relation completion is keyed by `RelationId` and current intrusion generation. | No circuit-certificate dirty owner, reverse dependency index, dependent observation withdrawal, or exact recertification path. |
| Memos and observations | `TypedPairMemo` retains endpoint-keyed children/witness/completion; context conflicts and relation completions are separate stores. | No certificate-generation dependency on typed memos, conflicts, derived bounds, diagnostic observations, or published scheme graphs. `pair_is_current` does not check a circuit-certificate validity state. |
| Publication and deferral | Candidate graph plans stage SCC member graphs before publication. Route transactions commit on `Ok` and roll back on `Err`. | No state that commits the new exact edge while suspending the private candidate result. Treating unsupported recertification as `Err` would roll back the required edge; treating it as ordinary `Ok` risks exposing stale results. |
| Rollback | `RouteMutationJournal` and `candidate_intrusion::Undo` restore existing row forests, parent records, relation completions, memos, candidate routes, and context/effect checkpoints. | Certificate revisions, dependency-index changes, withdrawn/recomputed observations, and graph publications are not currently owned by that journal. |

## Conditional omission witnesses

Assume an exact certificate recognizes component `q` at generation `g`, and
its dependency index correctly names an observation `o`, memo `m`, and
publication `p`. A late exact Function/swap edge `u` makes the complete
component fail both approved recognizers.

Required transition:

```text
(E, Valid(g), {o[g]}, {m[g]}, p[g])
  --retain u, dirty g, withdraw dependents-->
(E ∪ {u}, Deferred(g), {}, {}, unpublished)
  --route failure / rollback-->
(E, Valid(g), {o[g]}, {m[g]}, p[g])
```

Three minimal mutants distinguish the lifecycle obligations:

1. Retain one `m[g]` while withdrawing the other dependents. A memo read that
   checks only the equality/SCC generation can reuse stale evidence.
2. Retain `p[g]` after the edge is stored or recertification fails. A
   certificate-dependent candidate remains externally visible after its
   premise ceased to hold.
3. Restore `g` but leave `u` in the dependency graph. A later retry can reuse
   the old generation against a changed component.

These are conditional state-machine witnesses. They do not show that a source
program currently reaches a late-edge certificate state or that any current
route has these failures.

## Required implementation evidence

- Retain authentic inferred-entry provenance at its source owner; do not infer
  it from endpoint shape, annotation position, or a written interface.
- Recognize only the two complete approved circuit shapes and retain their
  exact generated SCC component, seeds, operation/attachment/filter identities,
  sharing links, count relation, and dependent observations.
- Mark a certificate dirty before a new dependency can reuse its observations;
  withdraw only observations depending on the old generation, retain the new
  exact edge/context, and run exact recertification.
- On unsupported recertification, keep exact private state and defer the
  candidate result without turning it into source rejection or ordinary
  success.
- Journal certificate/index state, withdrawn results, publication state, and
  the late edge together. Demonstrate rollback after withdrawal and a supported
  retry from exactly the restored dependency graph and generation.

An unowned review identified no missing semantic decision: the approved design
already specifies this lifecycle. No source implementation, tests, builds,
measurements, or code edits were performed for this audit. The prover agent
role was unavailable in the current collaboration schema; the conditional
witnesses above came from the available researcher lane and are not represented
as prover output or as a constructive source theorem.
