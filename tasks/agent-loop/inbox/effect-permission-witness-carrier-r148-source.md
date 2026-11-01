# R148 source correspondence — producer fields and the missing state association

Status: **FROZEN research handoff; writes STOPPED; independent review pending.**

## Objective, scope and result class

Assignment `R148-SOURCE`, author `/root/r148_source`, maximum 600 seconds. Sole
write lease: this file. Method: authenticate immutable inputs, inspect actual
producer/transport/consumer fields and operations, and give a conditional
information-loss discriminator. No executable solver experiment was authorized.

**Bounded source characterization:** source endpoint identity, relation ancestry,
physical bound readback, transformer support and FreshUse maps are retained.
Neither the inspected concrete effect producer nor its bound/relation/FreshUse
records supply an association between one actual contribution/member and its
incoming input/protection sets. The real allowance decision does not consume
such an association. This is an OPEN source/native application premise, not a
reachable source counterexample or a refutation of the original A/B claims.

The first deficit is already visible at the actual producer: operation signature
effect-member construction stores identity/provenance and an ordinary bound,
without incoming state for that member. It is not established that a previously
authenticated incoming state was discarded at a later call. Separately, the
explicit `Contribution` constructor has the same absent coordinates; its
FreshUse copy allocates a new instance while preserving effect/origin and an
external graph-node-to-new-endpoint map.

## Baselines, authentication and authority

Rust/Lean/design baseline: `3560df97dab02744da10e897c73c1cf94118f4ee`.
Accepted R147 artifact baseline: `b75eaf06bc51ed583650de5bad2e57cb400ba78d`.
Contract SHA-256: `6f44b8ab2fbf664a7acf6dc77940bc5ca7e7245495ff1fb215907659c470fc0a`.
Admission SHA-256: `24978efc978f41eb8400a900dd89d6b8e3312ae6c161374a6a4343c02a88fb2e`.
Contract/admission were read first as assigned, then hashed. All 15 admitted
source blobs and four R147 blobs were SHA-256 checked against the contract
before their substantive content was inspected. Read-only Git object commands
were explicitly confirmed by the primary; no Git mutations occurred.

Exact governing decisions used:

- Annotation integration, §1, §1.1, §1.2 and §4: composed polarity; local
  subtraction permission differs from actual inflow and actual Catch removal;
  unknown variables and later concrete lowers remain constrained; equal family
  or row identity alone creates no grant. Additional `write` survives a
  `signal` handler. Retain the same provider, assignment and typed position.
- Compose release, “Scope of the operation”, lines 34–56, and next discriminator,
  lines 76–82: release the matching `'e` protection also at its occurrences in
  output `'f`, including forwarding by `id`, preserve attribution and every
  independent protection, and create no capture permission merely by release.
- `rules/design-authority.md`, “Authority order” and “Natural compiler behavior
  and proof-obligation economy”; `rules/research-lab.pre-sprint.md`, “One semantic
  baseline”, “Writes, artifacts and review snapshots”, and “Evidence quality”;
  `rules/git-concurrency.md`, “Integration ownership” and “Disjoint-file mode”.

The accepted R147 review/outcome establishes only the bounded source boundary.
R146 proof conclusions were not read or used. No question bundle or historical
source outside the exact admitted set was consumed.

| Input at source baseline (Rust prefix `crates/yu-solver/src/`) | SHA-256 |
|---|---|
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean` | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |
| `notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean` | `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-15-compose-scoped-effect-release.md` | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |

| R147 input at task baseline | SHA-256 |
|---|---|
| `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-source.md` | `d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef` |
| `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-proof.md` | `f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010` |
| `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-review.md` | `b9bcd8bf2bebca4b063bcef24e8b9094eb40c525db0cbe48930631aab47316ed` |
| `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-outcome.md` | `e72267fe9da32b8a1408ce85a25056cfcc7888bc7045fd9fecc9555c56003595` |

## Concrete ownership and updates

All Rust locations below refer to the immutable source baseline, not current
working-tree line positions.

### 1. Actual effect producer and explicit Contribution

`candidate_source.rs:1731,2515` schedules/dispatches `Action::Operation` to
`candidate_operation`. `candidate_effect.rs:1112–1129` reconstructs the operation
signature using `SignatureContext::Operation { declaration, owner, occurrence,
retained_bytes }`. At `2398–2405`, the declaration's family is added to the outer
operation result effect. `candidate_signature_effect:2429–2448,2521–2557` creates
a view and an ordinary `Support(view)` bound on a fresh effect port. Support
expansion later emits `AnnotationMember(view, member)` at `1444–1458`.

The real identity owner here is `View` (`203–211`): `closed_weight`,
`source_weight`, `provenance`, `owner`, `position`, `allowed`, `tail`.
`ViewOrigin::Operation` retains `OperationOrigin { declaration, occurrence,
retained_bytes }` (`182–190`). `candidate_signature_view:1059–1097` allocates
view ID by append index and stores those fields. Member ordinal selects a
resolved `SourceEffectId` from `allowed`; it is not by itself evidence of
constraint-derived inflow or local subtraction permission. Neither the view
nor this constructor associates that member with incoming route/protection sets.
This is the earliest actual producer association absent in the inspected route.

The separate `Contribution` record (`176–180`) contains exactly:

```text
effect: SourceEffectId
origin: SourceNodeKey
instance: u32
```

`candidate_effect_contribution:1413–1435` takes only `(effect, origin)`, sets
`id = contributions.len()`, pushes `instance = id`, and returns
`EffectEndpointKey::Contribution(id)`. It has no input-route, scope, initial
protection, current state, or permission-owner field. The only non-test call
located across the nine admitted blobs is the FreshUse copy at
`candidate_scheme.rs:4598–4601`; this search does not establish an initial
source-reachable Contribution producer outside the admitted set. Test-only
callers were not used as source reachability evidence.

### 2. Relation and processing records

`candidate_context.rs:285–310` defines:

```text
ScopedDemand = { original_call, use_instance, root, output_scope, input }
ScopedFlow = { transformer, demand: Option<ScopedDemand> }
ScopedObservation = { relation, operand }
RelationKey = { pair: TypedPairKey, context: ContextId,
                sources: Option<usize>, scoped: ScopedFlowId }
Relation = { key, previous_on_pair }
```

`relation_with_scoped:3481–3512` interns flows and then the entire key, so equal
endpoint pairs with different scoped payload are not automatically one relation.
Effect relations reject deferred demands; Value relations reject nonidentity
transformers. `sources` refers to canonical sorted/deduplicated source-event
sets (`3514–3538`), not a per-member protection-state association.

Source call seeds retain call/root/use/scope/input at `3793–3838`. Function-port
projection checks the demand root and creates `stamp_input(input)` for
ArgumentEffect or `protect_body(output_scope,input)` for ResultEffect
(`3924–3987`). Explicit argument release uses the argument computation scope
(`3827–3832`). These construct transformations; they do not initialize a member's
incoming `ScopeState`.

There are two processing slots. `candidate_effect.rs:702–711` updates the
ordinary `Option<TypedPairKey>`; context `processing` is `Option<RelationId>`.
The live drain installs the relation before dispatch (`lib.rs:14199–14226` and
`14446–14464`). `candidate_context_execute:4208–4217` temporarily installs/restores
that relation. Thus metadata is accessible indirectly even though endpoint
calls have only two explicit arguments. The finding is based on field contents
and actual reads, not on signatures alone.

### 3. Physical bound and ancestry evidence survives

`BoundAdmissionCause` (`candidate_context.rs:598–603`) stores owner/extrusion
processing relations, or FreshUse `(antecedent, use_origin, source_bound,
mapped_relation)`, or bound transport `(antecedent, through)`.
`BoundAdmission` stores `(bound, origin, relation, group, cause, coverage,
previous_on_group)` (`606–610`). `BoundEmission` stores admission, bound,
physical slot, readback and previous emission (`613–617`). `EvidenceSnapshot`
retains source bound, relation, admission/emission heads and coverage (`677–681`).
`Dependency::Replay` retains ordered lower/upper relations and their input bounds;
`Transport` retains parent/child/use and optional `(from,to,reason)` witness
(`349–377`). `Origin` retains relation, source occurrence, inferred entry, formal
construction and optional source-drain receipt (`407–414`).

`candidate_insert_bound:635–643` in `candidate_extrusion.rs` records context
processing. Insertion obtains an admission before publication (`749–751`),
physically appends the bound, reads the addressed slot back, checks equality and
records the emission (`856–870`). `candidate_effect.rs:730–759` chooses the exact
FreshUse relation or constructs an owner relation; `BoundTransport` diagnostic
origins explicitly receive no relation in scoped mode. `candidate_context_bound_for`
(`4317–4354`) retains the scoped payload and source set in a child relation and
attaches it to the bound.

This evidence is not silently complete: `candidate_context.rs:867–886` marks
ordinary owner/extrusion admissions with `ProcessingAntecedentsUnavailable`,
`OrdinarySeedAuthenticationUnavailable`, and `MissingAntecedent`; FreshUse adds
`ReplayUseAntecedentsNotRetained`. Snapshot construction also exposes missing
relation/group/admission/emission gaps (`845–856`). None of these records adds
incoming input/protection membership for a contribution. Retention of a
processing ID does not authenticate the missing semantic association.

### 4. FreshUse preserves maps and endpoint attribution, not a member state

`candidate_source.rs:155–169,1870–1894` allocates scope/call-input IDs from append
indices and records region ownership. `ScopeInventory::from_plan:223–245` creates
origin/inventory vectors. `ScopeRemap:189–193` contains separate `regions`,
`scopes`, `inputs` maps. `ScopeInventory::fresh:296–357` appends copied IDs;
successful copied images are above the pre-copy vector lengths. An incomplete
failed copy may already have appended identities; no failure atomicity is
claimed. This allocator argument covers represented allocated coordinates,
not an unidentified incoming state's support.

`FreshUse` (`candidate_scheme.rs:772–790`) stores `scope_remap`, `scoped_relations`,
`context_use`, `rows`, role/field-tail obligation rows, lambda argument effects,
`terms`, `effect_operands`, `bundle_remap`, `context_remap`, `evidence_remap`, plus
test-only row observations. `RetainedFreshUseMaps:633–647` retains the same
relevant maps; `into_retained_parts:806–820` moves them intact.

Actual transformations:

- Capture retains original effect endpoints as graph nodes (`2154–2165`), and
  bound endpoint indexes, relation, source bound and captured snapshot reference
  (`2298–2326`).
- FreshUse creates one scope map before reconstruction (`4444–4451`). A captured
  Contribution copies `effect`/`origin` and gets a fresh `instance`
  (`4598–4601`); `effect_operands[index]` links its old graph-node position to the
  copied endpoint (`4605`). This external map preserves a reconstruction route
  for old/new attribution; the new Contribution itself contains no parent ID.
- Support/Allowance/AnnotationMember copies use the view map and retain the
  member ordinal (`4583–4596`). `candidate_copy_effect_view`
  (`candidate_effect.rs:1358–1378`) clones owner, position, operation provenance
  and allowed members, validates any source weight, and rebuilds the mapped tail.
- For each captured parent, `4773–4796` remaps the transformer's scope keys,
  stamps and guard tags through that one `ScopeRemap`, with identity fallback
  outside its domains. It separately maps demand output scope/input/root, and
  changes `use_instance` only for a locally mapped input. This transports no
  `ScopeState.inputs` or `.protections` field because none is present here.
- Imported snapshots populate `evidence_remap` (`4832–4835`); bound restoration
  uses the mapped endpoint, exact scoped relation and imported antecedent
  (`4861–4907`). `candidate_context.rs:4678–4708` checks the source bound,
  relation pair, nonzero use and exact FreshUse dependency before reuse.
- Replay unions source sets and composes lower then upper transformers,
  retaining upper demand (`candidate_context.rs:4455–4475`). It retains the
  operation, not the result of applying it to an authenticated incoming state.

`ScopeTransformer::remap` checks injectivity on transformer-local finite support
(`candidate_scope.rs:214–264`). The source presently supplies no member-state
support bound or same-map state remapping to join to it.

### 5. Reached decision and Catch connection

`candidate_context_execute_relation:4219–4243` reads the flow for the reflexive
guard and records `(relation,operand)` observations. Ordinary context filters
then select allowances; an existing row bound gains provenance and is replayed,
otherwise `candidate_apply_effect(lower,Allowance(view))` is called
(`4245–4303`). `candidate_extrusion.rs:1147–1170` inserts/replays row bounds or
reaches `candidate_check_effect_operand`.

The decision at `candidate_effect.rs:1478–1498` obtains the contribution's
`effect` or annotation member's resolved effect, then tests it against
`context.allowed(closed_weight)` or `view.allowed`. It accepts membership,
forwards an unmatched lower to a tail, or reports mismatch. Empty allowance also
mismatches at `1500–1503`. No branch reads incoming route membership or protection
membership, or evaluates the scoped transformer for a carried witness.

Catch is in this graph: `candidate_source.rs:1608–1623` propagates scrutinee/arm
effects outward; `Action::CatchOperation` dispatches at `2513`.
`candidate_catch_operation_inner` builds payload/response/continuation endpoints
and ordinary effect constraints (`candidate_effect.rs:1188–1283`), including the
annotation allowance at `1237–1249`. `constrain_live_effect` and candidate
`apply_effect_task` share the generic worklist (`lib.rs:13805–13841`). None of
these inspected owners performs protection-sensitive Catch subtraction. Static
route connection is established; no concrete fixture was executed.

`ScopeState` itself exists (`candidate_scope.rs:37–40`) with `inputs` and
`protections`. The evaluated state in `CandidateScopedObservation`
(`shadow_apply.rs:1301–1309,1646–1653`) is constructed by
`evaluate_observation` over empty slices (`candidate_context.rs:3280–3284`).
It is an observation result, not a retained actual incoming member state and
not an argument to the reached effect/Catch decision.

## Conditional derivation and exact falsifier

Candidate premise C: the full intended member-state semantics can be obtained
from a retained transformer/demand alone, by evaluating its empty observation.
The source has not established C.

A minimal guard discriminator uses one scope `s` and one tag `i`, with
`T = protect_body(s,i)`. Directly from `candidate_scope.rs:106–118,180–209`:

```text
evaluate(T, inputs=[],  protections=[]) = (inputs=[],  protections=[s])
evaluate(T, inputs=[i], protections=[]) = (inputs=[i], protections=[])
```

The same endpoint/family and transformer therefore permit distinct protection
results if the actual initial tag membership varies. The observed empty-state
value alone cannot determine both. Even identity requires retained inherited
protections: identity on `([],[])` differs from identity on `([],[s])`.
These are conditional algebraic witnesses against reconstructing arbitrary
incoming states from the transformation alone; reachability of both states for
one source endpoint is **not** proved. They are not source-program
counterexamples and were not run as an executable experiment.

The precise blocker is the unestablished association
`actual source member -> incoming (inputs, protections)` and its preservation
to the decision. The first concrete owner needing this association is the
signature effect-member producer/ordinary bound admission described above; the
separate Contribution allocator also lacks it. No statement here chooses a new
carrier layout or language meaning.

Necessary correspondence coordinates, wherever an approved representation
retains them, are:

1. Actual member/contribution identity, resolved effect identity and attribution
   (source owner/declaration/occurrence or position, member/instance, copy-use
   correspondence). A declared permission alone is not actual inflow.
2. Its actual incoming input-route set and protection-scope set, including
   inherited/independent protections; the allocating inventory/owner and bounds
   on those coordinates, and relation/physical-bound identity tying them to
   this member rather than a sibling same-family member.
3. The exact retained transformation and ordered processing ancestry; the same
   successful FreshUse scope/tag maps applied to both transformation and state,
   with external identity fallback justified on their combined support.
4. Source-owned local annotation/permission and selected endpoint/member
   association needed by the actual subtraction decision; output/residual
   membership preserving unaffected witnesses and scopes, including the output
   occurrence required by compose forwarding.

These are evidence obligations, not instructions to implement a new record.
The Native `State` definition (`NativeScopeTransformer.lean:71–74`) and
`Transformer.evaluate:126–132` corroborate only the formal state dimensions;
this source lane supplies no theorem-type/axiom audit and assumes no Lean/Rust
correspondence.

Concrete falsifier for this finding: an admitted, reachable consumer reads an
authenticated per-member incoming-state encoding from its actual producer,
renames both state supports with the exact FreshUse map, and changes its
protection-sensitive effect/Catch result while retaining that member's
attribution. The member state may be encoded indirectly; absence of a struct
named State is not the criterion. Existing relation IDs, source sets, weight
allowances, demand and empty observation do not establish that chain.

## Operations, coverage, resources and stop receipt

Reproducible authentication: `git show <baseline>:<exact-path>` captured in
memory by `python3` standard-library `subprocess.check_output`, with
`hashlib.sha256` compared to the contract. R147 names were located by read-only
`git ls-tree -r --name-only b75eaf... tasks/agent-loop`, then authenticated.
Source inspection used in-memory regex symbol searches and numbered windows;
all source locations above were read directly at the source baseline.
`candidate_intrusion.rs` was hash-read and symbol-searched, without a semantic
audit of its complete body. The other three Lean blobs were authenticated only;
the proof lane owns their theorem checks. Some broad combined outputs truncated;
the material field/operation windows were reread in bounded output calls.

One initial authentication command used unavailable `python` and failed before
reading source; rerunning with `python3` authenticated all listed inputs. One
window printer requested line 1173 after extrusion's line-1172 EOF and stopped
with `IndexError`; the bounded callee window and subsequently omitted scheme
windows were reread successfully. These are extraction failures, not solver
failures. No source execution, mutation probes, random seeds or search ranges
were used. Coverage is the named static producer/transport/consumer trace, not
exhaustive source reachability.

No independent Oracle was executed. Accepted policy is the semantic authority;
the conditional discriminator derives from the same inspected Rust algebra
and cannot independently validate source transition rules. No claims about
Oracle agreement, runtime outputs or whole-language completeness follow.

Resource cap: 600 seconds; first recorded clock during this lane was
`2026-11-01 03:05:45 UTC`. Exact dispatch-to-first-clock duration, CPU and peak
RSS were not instrumented; only small sequential text/hash processes ran.
No Rust/Cargo/Lean/Lake execution, build, test, compiler/Lean edits, descendants,
environment, checkout/worktree, scratch/cache, index/ref operation or Git
mutation occurred. No dirty/quarantined Rust was inspected. Only this leased
artifact was created. Final wall-clock receipt/hash is reported separately.

The artifact is frozen at this write. **All writes STOPPED**; no descendant or
other path remains active. Original A/B, source/native hygiene, whole-language
soundness, principality, semantic approval and production gates remain OPEN.
Recommended next action: fresh review authenticates this producer-to-decision
trace together with the proof lane's exact theorem premises, then the primary
admits only the first source-owned association/construction obligation that
remains unsupported.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/effect-permission-witness-carrier-r148-source.md`.
- Source baseline: `3560df97dab02744da10e897c73c1cf94118f4ee`; task baseline:
  `b75eaf06bc51ed583650de5bad2e57cb400ba78d`.
- Dependency hashes changed: none; authenticated hashes listed above.
- Claim/review status: bounded source characterization plus conditional algebraic
  discriminator; unreviewed, frozen; no theorem or production promotion.
- Checks run: 15 source and four R147 SHA-256 matches; pinned source symbol and
  field/operation reads only. No tests/builds/checkers run.
- Proposed commit message: `research: locate R148 effect witness state association gap`.
- Shared deltas deliberately left for primary/curator: accepted field-to-theorem
  mapping, exact missing association owner, dependency/gate status, resource and
  runtime disposition, review/outcome/current-state records. No shared task,
  authority, index, question bundle or manifest was edited.
