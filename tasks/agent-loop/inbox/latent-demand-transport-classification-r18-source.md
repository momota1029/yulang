# LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r18 — source handoff revision 1

Assignment `LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r18-source`; revision **1**. Sole author `/root/latent_demand_transport_classification_r18_source`; no coauthors or descendants. Requested **Sol/high**; observed model/effort **UNKNOWN**. Original grant **300 seconds**, started `2026-10-28T13:11:47Z`; no reset. Sole output lease is this handoff. Outcome: **complete finite row/source mapping; native evidence obstruction located; parent OPEN**. Producer evidence, not independent certification. **FROZEN / STOPPED** after this receipt.

## Authenticated inputs and correction

Contract `tasks/agent-loop/sprints/latent-demand-transport-classification-20261028-r18.md`, SHA-256 `fedd227744b66af19d5544315130233c4fb666667c996fcafa92dbb8ebf99e9a`; manifest `tasks/agent-loop/sprints/latent-demand-transport-classification-20261028-r18-inputs.json`, SHA-256 `d07167958cdb5f93a5370d48568a7a0ab4afc8b8ec31a02ffbdb359848a5b455`. Read-only SHA inspection authenticates **all 32 parent artifacts and 445 unaffected file pins**. The sole candidate differs from the inherited baseline pin `f0f8c15a78620ff34c85433fefbf842f4b716831207057a1804e7a27f2f77a3d` exactly as the admitted R18 implementation delta: frozen R18 `isolated/latent-demand-transport-classification-r18/crates/yu-solver/src/candidate_scheme.rs` SHA-256 `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`. Its implementer handoff, author `/root/latent_demand_transport_classification_r18_implementation`, authenticates at `2a81d84ddd55dcabb97ef2c7f91280c35dac83d8c06530a5e9154cd1fc7c9f2b`. Baseline pin mismatch is therefore recorded as the authorized candidate delta, not an assertion that all baseline bytes remained equal.

The four frozen files under `isolated/latent-demand-transport-classification-r18/logs/` authenticate:

| File | SHA-256 |
| --- | --- |
| `r18-cargo-1.argv` | `6d129811f7c96496371f3d1f17e1ad7890cbe7255f1c5e95a14005b83b49c990` |
| `r18-cargo-1.resources.json` | `0003cf316ccc09e747df3f7c17d9219e4f85ded598dfdaa7b31f6871c8528a1f` |
| `r18-cargo-1.stdout` | `37ba7e01469be1e9f6f00d57256abb9e49dda53bfbeea1e7bf611f684a0ddaf4` |
| `r18-cargo-1.stderr` | `ec10657838ff7912bb520a621eee1994be6d413d2e2ce7d234d209e122c6f27c` |

Luna's START message transposed two characters of the stdout hash. This worker reported the mismatch; Luna explicitly corrected and ACKed the actual hash above, stating the file bytes were unchanged. The mapping uses that corrected authenticated pin.

Reused R17 source revision1, sole author `/root/latent_demand_transport_classification_r17_source`, SHA-256 `ecd1c05c20f6888e6148109157d8bdc460999df3a9cf3767bc331f76841f2797`, only for source/constructor mapping. Its R16 coordinates were antecedent evidence; every numeric coordinate below is re-observed in **R18**. R17 did not run Cargo and is not execution evidence. R14 same-graph retention and R16 successful root reconstruction do not certify transport adequacy.

## Original parent and governing source

`YulangClosure.SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean:128`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`, retains this type:

```text
forall s x d a, p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e and p.sameScoped s x e a.
```

This is an uninstantiated proposition definition; no concrete proof or Lean check is claimed. Preserve independent F1/FK1, foreign-continuation, arbitrary lawful client-allocation, original scoped shared-witness and complete Call quantifiers.

Governing Generalize selection `notes/design/2026-10-08-source-generalize-definition.md`, SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`, selects `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1,3.3,5.1–5.2, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`. Call requires original callee computation, inert whole argument, actual returned callee, current receiver/receipt, actual entry, designated consumer and invocation return. Generalize preserves the entire simultaneous component, fixed provider/Established/OneShot dependencies and one original Shared binder. Independent frames allocate only eligible Desc declarations at their original scopes, ViewLogic before challenges, and EventProof under actual events. A numeric root map and successful local guards prove none of these universal source laws.

## Complete actual row inventory

The exact fixture at R18 `candidate_scheme.rs:8158–8160` is:

```text
my invoke f = f 1
my id x = x
my first = invoke id
my second = invoke id
my outer z = { my local h = h z; my first_local = local id; my second_local = local id; second_local }
my local_first = outer 0
my local_second = outer 1
```

All terms below have arena brand1; R12 trace invocation1. R18 stdout lines24–28 inventory four Replay dependencies and their per-row diagnostics. Lines33–48 contain **four paired starts/ends and eight callbacks**, precisely two callbacks for each full row tuple. **Zero skips**, **zero accepted events**, **zero returned evidence**. Each sequence is `MatchingRoute` then `Rejected("positive-function-node-absent")`, with end `observer_callbacks=2 returned_evidence=false`.

| Row | Source Call occurrence | Actual copied use and observed route | Replay child/lower/upper | Copied negative root; scope/input | Lower positive root; owner ValueRow |
| --- | --- | --- | --- | --- | --- |
| 0 | call0, expression1, occurrence2, `f 1` inside `invoke` | use1; Module route0 | 61/58/35 | 299; 32/8 | 310; 44 |
| 1 | call0, expression1, occurrence2, same source `f 1` | use3; Module route2 | 119/116/93 | 338; 38/9 | 349; 50 |
| 2 | call3, expression6, occurrence22, `h z` inside `local` | use5; Local route0 | 191/188/168 | 393; 44/10 | 402; 56 |
| 3 | call3, expression6, occurrence22, same source `h z` | use7; Local route1 | 248/245/225 | 430; 50/11 | 439; 61 |

The original source occurrences are observed by R12 capture/lookup trace lines53–65; the native interfaces in each row diagnostic have original demand264 for call0 and366 for call3. Two children per original Call invalidate call-only uniqueness. Module copied uses belong to the fixture's independent `invoke` uses; Local copied uses reconstruct `local` with its captured outer `z`. Their use IDs are inference FreshUse identities, not runtime invocation/event identities of `outer 0` or `outer 1`.

Exact numeric copying-source occurrence12 is logged for Module route0/use1, the `invoke` occurrence in `first`; the displayed route census is explicitly filtered to Module uses1|2 at source lines8254–8255. It does not log the numeric copying-occurrence ordinals of use3/5/7. Those exact ordinals remain **unobserved**; do not invent them or interpret `source_use_identities=[]` in rows1–3 as absent routes. Actual classification supplies Module route2/use3 and Local routes0/1 uses5/7, independently of that restricted census. The source Call occurrences2/22 are fully identified for all rows.

## Captured, imported and physical constructor chain

The same-run capture-to-lookup joins are:

| Rows | Source relation/root; original scope/input | Capture graph/node; bound ordinal | Capture source ValueRow; admission/emission heads | Imported snapshot -> FreshUse admission/emission -> replay upper |
| --- | --- | --- | --- | --- |
| 0 | 8/264; 1/0 | graph3/node11; ordinal3 | ValueRow38; 6/6 | snapshot3 -> 33/33 -> relation35 |
| 1 | 8/264; 1/0 | graph6/node11; ordinal3 | ValueRow38; 6/6 | snapshot3 -> 90/90 -> relation93 |
| 2 | 150/366; 15/3 | graph9/node12; ordinal4 | ValueRow41; 146/146 | snapshot18 -> 164/164 -> relation168 |
| 3 | 150/366; 15/3 | graph11/node12; ordinal4 | ValueRow41; 146/146 | snapshot18 -> 220/220 -> relation225 |

Graph identities are joined through actual trace/context_use, not equality of graph-local node11 or12. Source captures retain `EvidenceCoverage { gaps:56 }`. Each observed FreshUse admission has its own `coverage.gaps:120`; that destination record does not overwrite the capture coverage or close a missing coverage bit. Its cause names exact antecedent, use_origin, source_bound and mapped_relation. All four physical destinations are the table's owner ValueRow in `ValueUpperAtom`, index0, with exact copied negative root read back in `ConstructorAfterAppend`. Distinguish source EvidenceSnapshot, imported EvidenceSnapshotId, admission and physical append/readback.

Per-row `upper_lineage` explicitly retains Transport(parent8 or150, child35/93/168/225, use1/3/5/7, reason FreshUse) with original/copy bound endpoints. Replay then combines that upper with its separately observed lower. Lower owner-emission admissions/readback are 56,113,184,240, respectively, keyed by lower58/116/188/245. Those lower producers exist in this output even though full transport evidence returns None.

Owning paths in frozen R18 source:

- `shadow_apply.rs:4130–4168` constructs the four-port negative demand and joins original source registration into `NativeInterface`. `candidate_context.rs:3541–3583`, `candidate_context_seed`, local slot0 installs source-owned `ScopedDemand` with original use0.
- `candidate_scheme.rs:2761–2787` captures source relation/demand; `:2913–2948` retains the same graph's negative Function index. `prepare_candidate_fresh_use`, `:4650–4758`, reconstructs the indexed demand, remaps scopes/inputs and local use, imports evidence snapshots, and retains scoped relation maps. `begin_candidate_fresh_bound`, `:4760–4810`, constructs exact FreshUse transport and admission antecedent.
- `candidate_scheme.rs:1550–1579` publishes completed Local routes with their occurrence/use and retained graph/maps; Module publication at `:4868` retains use_id/graph/maps. These are separate owner families.
- `candidate_context.rs:3054–3063`, `replay_demand_rows`, retains each Replay dependency independently. `:3065–3079`, `fresh_use_witness`, requires unique exact FreshUse lineage; `:3085–3201`, `authenticate_replay_ancestry`, checks source/fresh/replay relation incidence, retained ordered replay, lower without demand and upper/child with copied demand, and typed FunctionPort operation/transformer contents. The source row diagnostics show both lower/upper matches true.
- `candidate_scheme.rs:967–1129`, `authenticate_demand_transport_observed`, is the consumer; fixture loop `:8417–8476` forwards the same returned Option into `emission_cases`.

## First failed native premise and exact limits

For **each** row, reaching the rejection at `candidate_scheme.rs:1094` means the same invocation passed preceding checks for: matching actual/retained use; original indexed negative root and copied term; unique captured source relation; bound/snapshot import equality; zero source/retained demand transformer; scope/input remap; negative Function and four ordered copied ports; unique FreshUse witness; physical emission/owner/lane/readback; retained replay recipe; replay ancestry including actual port-transformer contents; copied replay upper root; and positive/negative replay endpoint kinds. These are conditional conclusions about this immutable authenticator execution, not a complete source theorem.

At `:1085–1094`, `find_function(positive_root, Positive)` searches **the matching route's captured graph**, requiring its retained reconstructed term to equal the replay lower positive root. It returns None for either **zero matching nodes or more than one matching node**. Thus the exact obstruction in all rows is:

```text
cannot select exactly one same-route retained positive Function node
for replay lower roots 310 / 349 / 402 / 439, respectively.
```

The emitted word `absent` does **not** distinguish absence from duplication. The output contains no complete positive-node census for those graphs; it cannot decide which case occurred. No change to the guard or node-selection semantics is proposed or authorized here. The separately logged lower producer/readback does not imply that its positive Function occurs uniquely in the captured callee graph. Its construction ownership and the scheme graph's ownership must be connected explicitly.

The rejection macro at `:982–987` returns None from the **whole authentication call**. This is different from `original-root-absent`, which can continue traversal. Each row's later routes are therefore **unvisited**, not exhausted. Earlier routes that fail the use predicate emit no events. The one matching route per row in this trace is not a census proving global route uniqueness. All later negative-node selection, typed port-pair equality, evidence construction and multiple-matching-route checks remain unexecuted. Existing ancestry checks separately name p1, h, q and C; their supported zero-step incidences establish no general rewritten consumer spine.

`session.execute()` is observed Ok (stdout66/68). The test then panics at source8479 while selecting the first element of empty `emission_cases`. Therefore **one failed focused fixture**, not a successful validation or semantic counterexample. Runtime receipt: Cargo exit101, wall113.768s, sampled CPU44.22s, peak RSS1,890,820,096 bytes (1.761GiB), affinity0, no limit termination; invocation UTC `13:09:11.082970Z`–`13:11:04.850706Z`. These measurements belong to Luna's monitored Cargo process group, not this leaf.

## Application, mutual TODOs and stop receipt

R18 replaces R16's unlocated empty-Option observation with an owner-specific first failed **native selection premise** for every Replay row. It supports successful finite capture/import/physical/ancestry checks up to that premise. It supplies no all-source constructor law and no source-qualified counterexample: failed private evidence extraction alongside a successful inference session does not establish an incorrect inferred typing.

`R18-POSITIVE-NODE-UNIQUENESS-1` — owner Luna/source-native intake; exact next bounded packet: connect the actual lower owner-emission constructor and its positive Function/ordered port certificate to the matching FreshUse graph consumer, starting with the four frozen row tuples. First decide zero-versus-duplicate matches from the owning graph/retained maps and actual positive producer; preserve separate route/provider/witness identities. Minimal evidence TODO, not production implementation: retain or inspect constructor-supplied typed node/port ownership sufficient for the existing selection premise. Falsifier: zero/multiple same-route matches, or a producer from an independently owned graph without an approved typed bridge. Do not weaken inference, merge unrelated graphs by numeric IDs, or repair/retry R18. New instrumentation or lease changes return to Luna.

`R18-SOURCE-CALL-1` — owner Luna/source proof: derive original scoped Call/Generalize constructor-to-consumer laws with full provider/shared/world/event telescopes, independent F1/FK1 and foreign continuation cases. Earlier source-fixed first-call and value-Generalize emission audits are reused only within their lawful-old-interpretation/local-law premises; they do not prove arbitrary client allocation.

Luna owns post-run independent review, CLOSED_INCOMPLETE disposition required by the failed-test contract, records and Git. All `InferenceSoundness`, Call/shared-witness, Generalize allocation, complete source/native correspondence, effect hygiene, principality, termination and production gates remain **OPEN**. Approved Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization are preserved.

Checks by this leaf: read-only source/authority/log inspection, SHA-256 authentication and finite text inventory only. No tests/build/Cargo/Lean/Git/checker, production/source edits, descendants or background services. No Lean proof or axiom audit assigned or claimed. New/scratch paths: **only this exact handoff**. Writer stopped after freeze; no resumed grant or ongoing work claimed.
