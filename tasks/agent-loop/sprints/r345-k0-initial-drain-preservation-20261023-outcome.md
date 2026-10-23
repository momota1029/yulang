# R345 outcome — K0 initial-drain obligation preservation

**Disposition: bounded PASS for the contracted D2 family.** The frozen
candidate proof and independent review establish same-row-set solution
preservation for successful ordinary K0 initial/current/designated/processing
and FunctionPort transitions under the unchanged R336 L0 and R337 J premises.
The result is accepted only at this boundary; it does not close full N or a
parent theorem.

## Frozen artifacts and review

| Artifact | SHA-256 |
|---|---|
| R345 contract rev1 | `c4322952c7c484003ee7c85efeb63e3b6daf34a1efbb17b2d32ae532e5074fa8` |
| Primary read-only source census rev1 | `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b` |
| Proof candidate rev1 | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` |
| Proof handoff rev1 | `b46ff9cea2dfd7eaa1a9134e052c48b9abcd773538aba363950cf307cdc7467c` |

Fresh non-contributor `/root/r345_initial_drain_referee` returned **PASS** at
2026-10-23 09:04:13 UTC: no blocking, major or minor finding and no
source-qualified falsifier. The referee independently checked all 20
contracted proof/dependency/source pins; the four primary artifacts still
matched at review end. It also checked the inherited source pins for
`candidate_extrusion.rs`
(`80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`, pinned
by R338/R339) and `shadow_apply.rs`
(`f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`, pinned
by R337). These bytes match their inherited pins.

The review confirmed the decisive bounded arguments:

- Four coordinate maps establish both directions of the existing K0 Function
  rule, including comparisons derived through lattice rules and transitivity.
  The constructed children and their Swap/Preserve operations match the
  actual FunctionPort owners.
- A memo hit does not serve as its own witness. The first exact row admission
  completes its persistent bound append before another dispatch can observe
  the memo; ordinary replay queues work and does not re-enter dispatch.
- Authentic K0 source inputs, ordinary replay children and FunctionPort
  descendants receive distinct witnesses. The R339 two-bound replay witness
  is not assigned directly to a port child.
- Current, designated and processing transfers, reverse child-array progress,
  pending-to-queue handoff, acknowledgements, terminal retirement and exact
  restoration of the saved processing pair/relation preserve or entail every
  removed formula.
- Source admission remains `H_after = H_before ∪ {φ(q)}`. Duplicate identity
  does not prove equality. Fresh-row allocation uses an explicit restriction
  projection and is separate from same-row-set administrative preservation.

## Exact claim and interpretation boundary

For each successful administrative step in the authentic ordinary K0
source-initial / ordinary-replay / Function lifecycle, with inference rows and
term meanings fixed, the proof derives

```text
Sol(H_after) = Sol(H_before)
```

for the unchanged R339 independent algebraic interpretation
`H = B ∪ Q ∪ P ∪ R ∪ D`. It identifies the surviving bound, live slot, queue
item, replay child or Function consequence for each removed formula. It does
not treat cache membership, generation, completion, acknowledgement or source
history as semantic evidence.

`H` is not the whole-language semantics document's
`Vⁿ_{W,θ}` / `Cⁿ_{W,θ}` relation or boundary evidence `k`. Optional-record
concrete comparison remains non-transitive for this purpose. The aligned audit
revision is a context/crosswalk artifact only; it does not redefine `H`.

## Open obligations and implementation

The following remain **OPEN**: full N and cache/temporal/fiber coverage;
completed-source-constraint completeness; W/Z and model construction; S0's
existing premises and source-to-runtime composition; full C/M, F1/FK1, foreign
continuations, typed-view/boundary/effect semantics, principality, original
Simple-sub A/B, catalog and production.

No source-qualified compiler defect or safe implementation slice was found.
Disposition: `NO_SAFE_CODE_SLICE`. No compiler source, tests, expected outputs,
or provisional instrumentation changed. The review read relevant existing
test bodies as context only; it ran no tests, builds, Cargo, probes or Git.

Proof writer `/root/r345_k0_initial_drain_prover` stopped at 08:56:35 UTC;
fresh referee stopped at 09:04:13 UTC. Each full grant was charged
conservatively (proof 3000s, review 1500s); the primary census allocation was
charged 2400s. Integration remains within the reserved 300s. Runtime session
IDs and effective model/effort observations were unavailable and remain
UNKNOWN. No carryover or Astra use.

**Adjudication:** accept only this reviewed bounded D2 result. Apply it to the
R339 initial/current/designated/processing/FunctionPort remainder. Every other
parent claim and production gate remains open.
