# R126 source handoff — symbolic FormalEntry publication

Status: **FROZEN revision 3 bounded source-native evidence; independent review pending**.
No Rust edit, test, build, Lean run, checker run, or production claim.

## Revision 2 correction note

Revision 1 is preserved as the prior frozen handoff identified by SHA-256
`9b6b6ce90a5af4ecefd690ebdf3088c90944ca27d1c0a4fd8099ddc71e6a825a`. This
revision changes only the `U == T` fact-pair analysis and the `apply_effect_task`
locator. The corrected points are recorded below; every other revision-1 claim
and boundary is retained.

Revision 2 is preserved as the prior frozen handoff identified by SHA-256
`4370262af81c45413f09e27a99f5ab9a441b15a6dff57fec2759a1a798f181d4`. Revision 3
changes only the consolidated source locator inventory to match the already
corrected `apply_effect_task` locator above.

## Assignment and authenticated inputs

- Sprint: `EFFECT-PERMISSION-SYMBOLIC-PUBLICATION/20261102-R126`.
- Contract SHA-256: `8a999995dca10358d9a8aaf9db8a5e7b473edc0e199e9b0de3e066157e86d8cb`.
- Manifest SHA-256: `7e47ad03d3e49f8cf711d1c46d52a106179b1c86b40cd18ce0f2fb8c172cf155`.
- Baseline: `e4570173a19ed72f6257fa391032f153ca43943d`.
- Assignment: `R126-SOURCE-1`, handoff revision 3; sole output lease is this file.
- Worker: `/root/r126_symbolic_source`; current assignment session R126. Launch evidence: parent `NEW_TASK` assignment and primary check-in. Requested model/effort: `gpt-6-luna` / high. Effective observed model/effort: **UNKNOWN** (runtime metadata unavailable).
- Each Rust SHA-256 below was recomputed from only `git show e4570173a19ed72f6257fa391032f153ca43943d:<path>` and matched the manifest:
  - `crates/yu-solver/src/candidate_effect.rs` — `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`
  - `crates/yu-solver/src/lib.rs` — `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`
  - `crates/yu-solver/src/candidate_context.rs` — `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
  - `crates/yu-solver/src/candidate_intrusion.rs` — `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
  - `crates/yu-solver/src/candidate_extrusion.rs` — `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
  - `crates/yu-solver/src/candidate_scope.rs` — `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`
  - `crates/yu-solver/src/term.rs` — `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- Reused and rehashed the R125 source/proof/outcome dependencies: `0fc58726d0db552c99714926533080d0238cb913f3d898f1b12430b3057e84a3`, `23ac34427928c0f9e6a4060018391b0083de2da3c19381667950e763a9013387`, and `0cd54c5bcc0698657fdd6c16e00836dbdd35103f92fb2202ba0854d40dc7807e` respectively. R39 remains at its manifest-pinned commit/hash; this lane adds no R39 declaration or claim.

## Actual admission, drain, and permission frame

The relevant owner is `candidate_effect.rs::candidate_formal_entry_annotation` (1762–1828). It obtains the outer annotation effect row, rejects more than one symbolic variable, checks the registered computation formal/owner/scope/recipe/source Lambda, and rejects an occupied formal domain or an already retained permission for that registration. It takes `entry_effect` from that registration. For nonempty concrete permissions it clones the complete ordered `SourceEffectId` Vec into a prepared `FormalEntryPermission`; duplicates remain. The prepared permission is local and is not yet in the graph Vec.

For one symbolic name, the call sequence is:

1. `candidate_formal_effect_variable` (1543–1561) looks up the exact `(AnnotationScope, name)` key. On a miss it reserves the map/journal, calls `fresh_effect_at_level`, and records the new row; on a hit it reuses the mapped row. The helper can fail before any direct constraint is admitted.
2. `candidate_formal_effect_equal(occurrence, 45, entry, tail)` (1750–1760) iterates `[(entry,tail),(tail,entry)]` in that order. For each pair it constructs a positive lower live-effect term and a negative upper live-effect term, creates the exact occurrence slot, derives the matching `CauseId`, admits/records provenance, then constrains the canonicalized effect endpoints.
3. `constrain_live_effect` calls `constrain_live` and, with the candidate graph enabled, `run_candidate_typed_drain` (`lib.rs` 13805–13813, 14045–14344). The synchronous drain starts a `TypedDrainFrame`, seeds context, enqueues the typed effect task, repeatedly transports it through candidate context, executes/consumes context, dispatches the effect, and drives any function/tuple/record/variant children. It then closes diagnostics and replay acknowledgements; terminal return records a completed source-drain receipt if present and pops the frame (`candidate_context.rs` 59–119, 2401–2428; `lib.rs` 14959–15031). On the effect branch `apply_effect_task` dispatches to `candidate_apply_effect` (lib.rs 13815–13823); that canonicalizes endpoints, may suppress an equal-endpoint operation, or inserts/replays the typed bound (candidate_extrusion.rs 1147–1170). This changes solver/effect/context state, not the retained FormalEntry permission Vec.
4. Only after both calls return success does the outer helper append the prepared permission (candidate_effect.rs 1812–1828). The final resource sample happens after this local append and can still fail; this handoff does not equate local success with whole-call success or atomic publication.

Let `V0` be the actual `formal_entry_permissions` Vec immediately before the optional symbolic helper, and `V1` its value immediately after that helper succeeds. The field is private to `candidate_effect::State`. Its complete logical-mutation inventory in the pinned owner is: this one `push` (1821) and checkpoint rollback `truncate` (533); all other uses are reads, byte accounting, or the checkpoint length. The typed drain owns context/replay/effect state and cannot name or mutate this private Vec. It does not re-enter `candidate_formal_entry_annotation`; no admitted helper path between the two timestamps calls its `push` or a rollback. Therefore, for every successful symbolic helper path, including memo/canonical suppression paths:

```text
V1 = V0
```

If concrete is nonempty, the subsequent permission append is `map P V2 = map P V0 ++ [build(a,f,r,entry)]`. If concrete is empty, no permission record is prepared/appended; the symbolic pair may still be drained. With no symbolic name, no drain occurs and the same append follows preparation directly. R125's same-Vec PRE witness and exact local-append analysis remain applicable; they do not prove a caller-wide rollback or the later consumer read.

## Exact direct request -> provenance -> retained term projection

Write `U = entry_effect`, `T = the exact row returned by candidate_formal_effect_variable`, `O = occurrence`, and `C_s = CauseId(ConstraintOccurrenceId(O,s))`. `live_effect_term` delegates to the branch term arena with `ComponentKind::Effect` and the requested polarity (lib.rs 10607–10613); `term.rs` 1205–1216 interns the full `(kind, polarity, ordinal)` view. `Term` equality includes arena brand and index (term.rs 102–114). Thus the original request terms, not reconstructed terms, are:

```text
request 45 = (C_45, lower = live(+Effect,U), upper = live(-Effect,T))
request 46 = (C_46, lower = live(+Effect,T), upper = live(-Effect,U))
```

The native `ConstraintOccurrenceId` preserves the full occurrence and local slot; `CauseId` contains that exact occurrence ID (lib.rs 424–463). Admission validates each term in this branch arena and requires same component kind (4007–4115). `candidate_formal_effect_equal` passes the exact `lower`/`upper` `Term` locals into `ConstraintStore::admit_and_record_provenance` before applying endpoint canonicalization, so graph representatives used by propagation cannot replace the retained direct request terms.

For a fixed successful invocation, let `P0` be the provenance length on entry to `candidate_formal_effect_equal`; let `F(t)` denote the actual fact whose ID is `t.index()` in `facts()`. The store transaction keys canonical facts by the ordered pair `(lower,upper)` and either reuses its exact existing `FactId` with `AdmissionDelta::Duplicate`, or appends one immutable `SemanticFact { id, lower, upper }` and records it as `Accepted` (lib.rs 4007–4090). Consuming either receipt always appends one provenance edge `{cause, fact}` (3797–3862). Therefore successful execution of both requests gives the ordered suffix:

```text
provenance[P0 .. P0+2] = [ {cause:C_45, fact:f45}, {cause:C_46, fact:f46} ]
F(f45) = (live(+Effect,U), live(-Effect,T))
F(f46) = (live(+Effect,T), live(-Effect,U))
```

This defines the direct-request projection from the retained edge to the retained fact by `edge.fact -> facts[edge.fact.index()]`; it retains typed endpoint identity, slots/order and one edge per request even when canonical facts were already present. The canonical fact Vec may gain zero, one, or two entries depending on prior exact endpoint pairs; if `U == T`, requests 45 and 46 have the same ordered typed term pair, so the second reuses the first request's canonical `FactId` and at most one fact is newly appended. If `U != T`, the pinned `Term` equality (brand/index) and live-variable interning (kind/polarity/ordinal) make the respective ordered pairs different, so there may be up to two newly appended facts. In both cases there are exactly two successful provenance appends: `C_45 != C_46` because their local slots differ. Other earlier provenance remains the prefix `P0`; typed propagation does not call the store admission method, so no propagated work interleaves in this suffix.

The frame is invocation-scoped: a prior failed attempt may have left an earlier edge with the same occurrence/slot if its enclosing route did not roll it back. Such earlier edges lie in `P0`; provenance is append-only multiplicity, not a globally unique slot index. The R126 projection uses the two-edge suffix for this attempt and does not infer uniqueness from `CauseId` alone. On success the R39 generated-link state can be interpreted as the ordered mapping of provenance edges through their `FactId` to these original fact terms; hence the direct helper's link suffix is precisely the two requested links. This is generated-constraint provenance, not external inflow or current effect lower storage.

## Failure and suppression cases

- The outer guard, missing entry effect, row with more than one variable, allocation/reservation/sample error, or failed annotation-tail creation returns before successful pair completion; no successful two-request projection is claimed.
- If request 45's admission fails, `admit_and_record_provenance` truncates any partial fact/provenance transaction and slot 46 is not attempted. If request 45 is admitted but its typed drain fails, slot 45's store/provenance entry can remain absent an enclosing route rollback; slot 46 and the permission append are skipped.
- If slot 45 completes but slot 46 admission/drain fails, slot 45 remains absent enclosing rollback, slot 46 has no committed edge on its admission failure, and the prepared permission is not appended. No generic all-state rollback is inferred from the typed-drain frame pop.
- A duplicate canonical fact suppresses a second fact allocation but still receives a fresh receipt and provenance edge. A typed-pair memo or canonical-equal endpoint can suppress propagation work while the direct request remains admitted. With `U == T`, the two requests have the same ordered retained typed term pair and may share a canonical `FactId`; their distinct causes/slots still produce two provenance edges in order. Effect endpoint canonicalization may also return equal endpoints and skip bound insertion.
- A resource sample after the permission push can return an error after the local append; outer route transaction rollback is not established here.

## Parent application, remaining edge, resources, and stop

Parent application: this closes R125's two exact source-owner TODOs for the bounded symbolic helper: successful drain permission frame `V1=V0`, and the ordered direct-request trace reconstructed through retained `FactId`/provenance edges to original terms. This supplies source equations for the proof lane to apply to existing `ComputationPermissionEntryR39` only. It is not a whole-language theorem, full effect-hygiene closure, actual-arrival/subtraction result, later consumer proof, or production permission. R111's 6 GiB private verification resource gate still blocks Rust integration.

No newly reached unpinned source owner. Source locators: candidate_effect.rs 143–148, 520–534, 1543–1561, 1750–1828; lib.rs 424–483, 3425–3464, 3797–3922, 4007–4115, 10607–10613, 13815–13823, 13805–14344, 14959–15031; candidate_context.rs 59–119, 2401–2428; candidate_extrusion.rs 1147–1170; term.rs 102–114, 1205–1216. `candidate_intrusion.rs` and `candidate_scope.rs` were hash-checked and only reached for their pinned ownership context; no additional FormalEntry permission mutation was found.

Checks were static `git show`/`rg`/focused line reads and seven manifest SHA-256 comparisons plus three prior-evidence SHA-256 comparisons. No tests/build/Lean/checker. CPU/RAM were not measured; no measured resource claim. No scratch/generated output, copies, environment/storage probe, dirty/quarantined read, worktree, Git mutation or delegation. Sole new path is this leased handoff; no disposable scratch remains.

Mutual TODO to proof owner: apply the above equations to only the existing R39 declarations, preserving full `Id` distinctions, exact invocation-scoped provenance suffix and all prior R125 premises; falsifier is any actual fact lookup or successful suffix edge that disagrees on cause, typed endpoint, slot, order or multiplicity. Required source owner: this frozen handoff plus manifest-pinned R39. Do not infer external inflow or later consumer behavior.

Frozen handoff ID/revision: `R126-SOURCE-1` / 3. Exact dependencies: contract, manifest, seven source hashes above, and the three R125 evidence hashes above. No next source step remains inside this assignment. Worker writes STOPPED at handoff freeze; no descendants or background process.
