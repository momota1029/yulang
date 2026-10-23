# Frozen handoff — R341 K0 source retention

Sprint-ID: `R341`. Contract revision 1:
`tasks/agent-loop/sprints/r341-k0-source-constraint-retention-20261023.md`,
SHA-256 `62cb4018db42e0266f0f357ed6f44c187d6397865905b68487fe143d00250769`.

Assignment-ID: `R341-K0-SOURCE-RETENTION`. Handoff revision: **1**.
Outcome class: **candidate source/native proof and S0 application**.
Frozen proof:
`notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`,
SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`.
This inbox's frozen byte hash is returned separately to Luna; it is not
embedded in itself.

## Parent and actual result

Unchanged parent: user audit §§4, 6 S0 and 10.3:

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
```

The candidate proves final-H retention of every authentic K0 source
inequality C_s, including the actual Definition-root `Action::Link`.
Every source inequality has a row endpoint. A completed-dispatch invariant
gives an exact persistent physical bound cell, or reflexivity, for each
corresponding memo key. Its proof checks exact identity extrusion, stable
representatives/generation, cache-before-append ordering, absence of reentrant
dispatch before append, physical slot readback, and source-drain retirement.
The source initial/current request retains q before append; the physical cell
retains q after append and frame removal. A cache hit uses the earlier
completed-dispatch witness, not the completion bit. Fresh and duplicate
successful admission both add q to H; FactId identity is not entailment.

All seven forms are quantified over authentic occurrences: Literal, enclosing
Value-Lambda parameter Name, Value Lambda, Apply, else-complete If, Group,
binding-free Block/StatementBlock. No first exception was found. Both If
branches and all condition/branch/prefix Effect inclusions are included.
The root uses body Value ≤ root Value, with no root Effect row or equality
between the two Value types.

Parent application: §7 defines the source-to-native construction map ι,
the kind-preserving final representative map μ, and
`ρ_s=(ρ∘μ)|D_s`. Its support includes nested Function rows, Lambda
entry/return Effects and Apply invocation Effects. Name semantic endpoints
select the authentic formal without equating the unused Name component to
it. Source-term induction transports satisfaction. Combining retained C_s
with reviewed R336 D1/G-sound and R337 J yields the exact S0 formula above
under its original four premises. S0 has no runtime/M premise.

This is not reviewed closure. The exact remaining acceptance premise is fresh
independent review of the new physical-witness invariant, source census and
row transport, followed by Luna adjudication. Full N, general Function/
Function cache and retirement, designated/foreign processing obligations,
W/Z/M, premise-free S0, source completeness, principality, original A/B,
catalog, I-publish and production remain OPEN. No source-qualified compiler
defect or implementation TODO is claimed.

## Source/native correspondence

- Constructors: `candidate_source.rs` emits Facts, recipes, ValueConstraints
  and the authentic root Link; parameter Names use their exact formal.
- Admission: `lib.rs::admit_collected_fact` / `admit_lambda_fact`,
  `shadow_apply.rs::admit_candidate_fact` / `admit_candidate_effect`, and
  `candidate_scheme.rs::admit_candidate_value_link_wide` all continue to
  live typed constraint processing after every successful store receipt.
- Processing: `start_typed_drain` → queue/current transfer → exact relation
  transport → identity context execution → `dispatch_live_item`.
- Physical witness: `candidate_apply_value/effect` →
  `candidate_insert_bound_with_evidence` → exact addressed readback → replay.
  Level-1 row/row inequalities use the lower row's negative/direct-upper
  lane; structured/atom lower uses the upper row's positive/exact-lower lane;
  row to structured/atom upper uses its negative/exact-upper lane.
- Retirement: ordinary replay enqueues before outer dispatch; acknowledgement,
  diagnostics, source-completion attribution and `ReturnReady` pop preserve
  the physical cell. Capture reads live bounds into a separate graph.
- Cache: `record_typed_pair_admission` calls `mark_candidate_pair` before
  apply. The stamp alone supplies no semantic fact; the completed-dispatch
  induction supplies the needed source-row witnesses.

Falsifier: an authentic NativeComplete K0 state S, exact occurrence q∈C_s,
the specified row map, and explicit ρ satisfying final H(S) but violating
μ(q). A hypothetical memo-only heap with no authentic history is not that
counterexample. An omitted reachable E memo/deletion/rewriting owner is a
blocking source-census finding.

## Dependencies and provenance

Baseline supplied by Luna: `d6610bb03cd1f9037df834982722e0022fc79209`.
No Git command was used. Contract, audit, dependencies and production pins
were read and byte-hash checked; source pins were rechecked before freeze.

| Dependency | SHA-256 |
| --- | --- |
| user audit | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R341 primary census | `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb` |
| R336 D0/D1 rev4 | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R337 context proof | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| R337 source census | `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a` |
| R339 replay-child proof, bounded reuse only | `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87` |

Exact production file hashes, including the R337-pinned actual Link helper
and recipe owners, are in proof §9. They match the R341 contract or inherited
R337 manifest. No new external dependency was introduced.

Prior work reused: R336 algebra/L0/D1/root subsumption and R337 J in their
reviewed authentic-prefix domains. R339 applies only to actual ordinary
bound-replay children; it does not certify this source root or a foreign
continuation. R338 disputed admission equalities and pending correction were
not assumed. R340 continuation theorem and pending S0/S0+M delta were not
used as premises. The proof retains the independent β/H interpretation.

Sole author/worker: `/root/r341_k0_source_retention_prover`.
No coauthors, contributing descendants, reviewer role or descendants' leases.
Requested model/effort: configured `gpt-6.1-sol` / `high`.
Observed effective model/effort: `UNKNOWN` / `UNKNOWN`.
Own runtime session ID: UNKNOWN. Containing primary session read from current
state: `4a30d8bc-cf58-442a-ac35-a6026b4e35b5`; not claimed as child session.

## Checks, resources, next step and stop

Checks: direct source/caller/mutator inspection, hand inductions and
`sha256sum` of frozen inputs and outputs. No tests, Cargo/build, execution
probe, network, nested CLI, model-policy change or child launch.
Grant: 2,400 seconds, no carryover. Exact launch/total active duration is
UNKNOWN; retain the full 2,400-second charge conservatively. First observed
clock: `2026-10-23 06:29:47 UTC`. Final dependency-recheck/freeze-preparation
clock: `2026-10-23 06:38:38 UTC`. This observed interval is not asserted to
measure the entire assignment.

Mutual TODO `R341-RETENTION-REVIEW-1`, owner Luna: freeze proof/census/sources
and assign the contract's fresh non-contributor reviewer. Challenge exact
identity extrusion, all production E memo/deletion paths, non-reentrancy
before append, and complete kinded support/transport into D1. Output is a
bounded disposition or first exact omitted source/consumer case and falsifier.
No production edit is requested. Any later provisional state-view/probe needs
Luna's distinct authority and resources; it is not licensed by this TODO.

Next in-scope step is the independent review seam and Luna intake. This
assignment ends here; it does not remain RUNNING while waiting. Outcome is
research-only and pending review/integration, not a production milestone.

Exact new/write paths are only:

1. `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`
2. `tasks/agent-loop/inbox/20261023-r341-k0-source-retention-prover.md`

No scratch, generated, central-state, compiler, test, expectation, question,
configuration, index, manifest or other-worker file was written.
**Writer-stop receipt:** after this final handoff write, both files are frozen;
only read-only output hashing and reporting follow. All writes stopped; no
descendants or unresolved descendant leases. Further edits require Luna's
explicit revision intake under the same or revised envelope.
