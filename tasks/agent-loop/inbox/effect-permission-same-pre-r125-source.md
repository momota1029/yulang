# R125 same PRE-state source handoff

Status: FROZEN bounded source derivation; independent review pending. Exact permission/Inputs correspondence derived below. Full graph-to-publication interpretation remains conditional at the generated-trace boundary; no source-reachable counterexample is claimed.

Session: `EFFECT-PERMISSION-SAME-PRE/20261102-R125`.
Worker: `/root/r125_same_pre_source`.
Baseline: `bf83716eea816536f3cc1d68b323d1567712dd38`, branch `yulang3`.
Exclusive changed path: this handoff only.

## Method and authenticated dependencies

Static construction/field-owner derivation from the R125 manifest. All eleven immutable source hashes and all eleven prior-evidence hashes matched by SHA-256 of `git show <manifest-commit>:<path>`. No dependency changed. Rust reads used only those immutable blobs. Corrected R39 is the manifest-pinned `1f5835c276143537ec58ed81db96c7c108cea8e7` blob. Governing root AGENTS files, research-lab rules and preserved baseline, design-authority, git-concurrency, and authoritative top-level inference principles were read. The primary selected the method and gate; this note selects no language meaning.

The claim concerns one actual invocation that reaches the relevant points in one existing session graph, not every abstract graph or arbitrary replay. R122–R124 lifecycle/uniqueness evidence retains its recorded scope. Local success gives the explicit guard facts without assuming that scheduling always reaches success. No global uniqueness/progress premise is added to this local implication.

## Native carrier and exact field interpretation

Fix the actual session object S, its immutable batch B, and its candidate graph G during the invocation. Use distinct tagged alternatives for complete native `SourceRootId`, `HirParameterId`, `HirOccurrenceId`, `SourceNodeKey`, `AnnotationScope`, `SourceEffectId`, symbolic-name text, and a raw effect-row coordinate belonging to this fixed S/G. This is a prose interpretation into R39's existing arbitrary `Id`, not a new Lean declaration or an added Rust token. For row coordinates, the interpretation is graph-relative: `row_G(n)`, never a claim that row n in another session is equal. The interpretation preserves native equality and distinguishes the alternatives; no ordinal/spelling/pointer-start conversion is used.

Native identity facts: HIR module.rs 1153–1156, 1184–1187, 1300–1320, 1377–1407 and 1438–1441 retain artifact-branded occurrence/root identities and root-plus-ordinal parameter identity. `SourceRootId` also preserves its Definition/Expression/Member variant. `AnnotationScope` equality preserves the enum alternative and payload (candidate_effect.rs 40–45). SourceEffectId equality is the derived equality of its `Arc<ModuleId>` and exact declaration `SourceNodeKey`; SourceOperationId equality additionally preserves the operation's declaration key and its full family (module/source_annotation.rs 32–51). The permission copies whole SourceEffectId values; it does not replace them with spellings, module names, operation ordinals, or SourceOperationId. No operation-level license is inferred from a family member, and this lane does not authenticate the separately owned implementation of SourceNodeKey/ModuleId equality.

Let R be the actual `registration: usize` argument, A the actual SourceAnnotation argument, O the actual occurrence, Q the actual scope. At constructor entry, E is A.ty.effects, F is B.candidate_calls.formals[R], K is F.recipe_position, and U is F.entry_effect when present. R39 action `a` maps these exact arguments: registration R, annotation owner/position from A, occurrence O, scope Q. The row r is the outer A.ty.effects, with exact position, concrete vector and symbolic-name vector. It is not a nested Function result row.

R39 registration f maps F.owner, F.lambda, F.parameter, F.recipe_position, F.scope, F.role and F.entry_effect directly. Its natural-number lambda, recipe and registration coordinates are precisely the vector indices used in Rust, not occurrence ordinals. R39 permission P maps every FormalEntryPermission field in declaration order (candidate_effect.rs 274–285): registration, parameter recipe, full formal identity, occurrence, source_owner, scope, annotation_position, source_row, graph-relative raw entry_effect and complete concrete vector.

## Inputs at the guard: one batch and one graph

Define t0 immediately before evaluating the combined guard at candidate_effect.rs 1773–1782, after obtaining row, registration and `exact_lambda_formal`. All facts below use G at t0.

* `e.formals = map registration B.candidate_calls.formals`, preserving Vec order and length. Thus `e.formals[R]? = some f` is exactly the successful `.get(R)` at 1765. candidate_call.rs 10–30 owns this Vec and its fields.
* `e.recipes = map parameterId B.parameter_recipes`, preserving its actual Vec order. The recipe equation is the native `.get(K) == Some(&F.parameter)` check at 1776.
* For `e.owners`, linearize the actual finite `B.candidate_source.source_owners` map once, preserving every complete key/value pair exactly once. No order fact is used: distinct keys make first-match lookup equivalent to `.get`, for any such linearization. In particular `ownerLookup e.owners O = some A.owner` means exactly the native `.get(O)` comparison at 1777, and the preceding F.owner == A.owner guard supplies the owner equality needed by R39.
* For `e.sources`, use one pair per distinct source-root key, whose value is the exact LocalSource returned by B.hir_for_source_root(root), then hir.local_source_for(root), when the resolver succeeds. Each expression vector is projected in its existing order; Lambda keeps its occurrence and parameter identity, all other forms become `other` with their actual occurrence. No HashMap ordering or independently equal-looking carrier is used. The successful native chain 1767–1772 is then exactly `sourceLambda e f = some (O,F.parameter)`. lib.rs 20406–20416 resolves the owning HIR using native root ownership; HIR module.rs 2022–2029 obtains its authentic retained LocalSource. The resolver-selected source is the witness, not an arbitrary other source with matching fields.
* `e.occupiedDomains` is any duplicate-free enumeration of the actual key domain of `G.intrusion.effect_algebra.formal_domains` at t0. Its only use is membership. Thus `K ∉ e.occupiedDomains` iff the native `.contains_key(K)` guard is false. Enumeration order has no meaning.
* Write `V0 = G.intrusion.effect_algebra.formal_entry_permissions` at t0, the actual Vec owned by candidate_effect::State (138–148). Then the exact equation is `e.retainedRegistrations = map registration V0`. Repetitions and order are retained. This is not B.formals or an inventory reconstructed from another graph.
* R39 schedules are irrelevant to Valid/sourceLambda and are not used to reconstruct the owner's Lambda index.

After this guard succeeds, F.role is Computation, F.owner == A.owner, F.scope == Q, the recipe and owner-local Lambda equations hold, K is absent from the actual domain, R is absent from the registration projection of V0, and r.variables.length ≤ 1. The entry check at 1783 supplies `f.entry = some row_G(U)`. These are exactly the existing `prepare_exact` premises after the above interpretation. They are t0 facts. No after-append absence fact is substituted for them.

Source construction corroborates the action binding: candidate_source.rs 1104–1118 append-allocates the actual registration/recipe and stores the owner-local expression index; 1323–1327 obtains R through the same parameter-registration map, uses the actual annotation clone, occurrence and retained scope, and 2463 dispatches those arguments unchanged. Annotation cloning preserves data; it does not make the copied concrete vector allocation identical to the original annotation allocation.

## Same permission Vec, timestamps, exact append and indices

Set `s0.permissions = map P V0`. Together with the Inputs equation above this yields the required shared-witness equation:

`e.retainedRegistrations = map (fun p => p.registration) s0.permissions`.

Both sides come from the same ordered retained Vec of G at t0. The equation is derived from the fields and their projection, not assumed from equal contents of two snapshots. No permanent vector-buffer address is required: `.try_reserve(1)` at 1806 may relocate that Vec while preserving its sequence and its field owner G. Therefore allocation-address equality before/after reserve would be an incorrect requirement.

For a nonempty concrete row, 1787–1790 reserve a new concrete payload Vec and copy `row.concrete.iter().cloned()` in full. This preserves length, every index and every duplicate. It deliberately creates new payload storage, so annotation and permission payload pointers must not be equated. Every remaining permission coordinate is copied directly at 1791–1802. The prepared record is held locally until symbolic preparation succeeds.

Define t1 just before 1818, after the optional symbolic helper returned success; define t2 immediately after the push at 1821, before scratch subtraction/final sampling. If t1 is reached with the prepared nonempty record, its data is still the copied record above. At t1→t2 there is only byte-counter checked addition and Vec push. Hence, writing V1 for the actual graph Vec at t1, the unconditional local sequence equation is:

`map P V2 = map P V1 ++ [build a f r row_G(U)]`.

The new permission's physical index is `V1.len()`, while its registration field is R. These numbers are not generally equal: Value registrations and empty-concrete computation registrations contribute to B.formals without appending this Vec. The actual model uses a list append, so it preserves this distinction correctly. R125 does not close the later R121 indexed-reader equation. `owned_projection_entry_permissions` enumerates the actual retained Vec with its physical indices (candidate_effect.rs 386–390). candidate_receiver.rs 1860–1867 later indexes its inventory by request.registration and checks both index and record.registration; this is a separate consumer condition and cannot supply the constructor's PRE witness.

When the symbolic-name vector is empty, no symbolic helper is called, and t0→t1 only allocates/prepares local data, reserves capacity and updates scratch bytes; therefore V1 = V0 and the full permission equation is `map P V2 = s0.permissions ++ [build ...]`. Empty concrete rows append nothing. The final resource sample at 1830 is later than t2 and can fail; local append is not whole-call success or atomic external publication.

## Symbolic helper effects and precise remaining bridge

For a singleton symbolic name N, candidate_formal_entry_annotation 1813–1816 reads the entry level, obtains a tail via `candidate_formal_effect_variable(Q,N,level)`, then invokes `candidate_formal_effect_equal(O,45,U,tail)`.

The first helper (candidate_effect.rs 1543–1561) either reads the existing annotation_effects entry keyed by the complete native (scope,name), or reserves and allocates a fresh effect variable, updates nested-byte/journal metadata, inserts that key→row, and samples resources. fresh_effect_at_level (lib.rs 10552–10581) appends effect bounds/levels/metadata/marks. Thus the helper really changes graph/session state even before generating an equality; it is not a read-only permission lookup.

The second helper (candidate_effect.rs 1750–1758) loops in the fixed order `(U,tail)` then `(tail,U)`, creates raw positive/negative live effect terms, constructs direct occurrence slots 45 then 46, admits each constraint with provenance, and runs constrain_live_effect. live_effect_term uses the branch term arena (lib.rs 10607–10613 and 10659–10684). effect_endpoint subsequently canonicalizes via the graph's actual effect representative (11901–11917, 13577–13582). The actual solver operation therefore cannot be identified with appending two raw endpoint pairs to its lower-bound store.

constrain_live_effect → constrain_live → candidate typed drain is visible at lib.rs 13805–13813, 14045–14089 and 14321–14343. The drain steps real constraints and can mutate the actual effect/intrusion state. The pinned intrusion implementation explicitly copies existing bounds and origins, updates effect forests, levels and metadata, canonicalizes/reopens/replays bounds (candidate_intrusion.rs 599–705). No preservation of existing lower-bound contents follows from this helper. On failure the shown typed-drain owner pops its frame and restores processing fields; it does not establish general rollback. The entry permission append is skipped if either helper fails before t1.

The whole-file private permission Vec mutation inventory in candidate_effect.rs has one push (1821) and checkpoint truncation (533). The entry body does not request rollback; the typed-drain wrapper's displayed error path does not truncate permissions. Nevertheless a complete transitive successful-helper frame proof is not authenticated by this lane: drain execution delegates to context/effect comparison owners outside the manifest. The unconditional symbolic permission append equation is therefore stated against V1 above. Using V1 = V0 across all successful symbolic drains still requires authenticating that relevant transitive path, rather than silently assuming it from direct writes in this function. The same caution applies to domain membership across the helper; Valid was obtained at t0 and does not require proving domain absence again at t1.

R39 State.links is explicitly a generated-constraint trace, and State.inflow externally supplied contribution data (R39 265–283). Neither is defined as the solver's current effect bounds. The displayed call sites establish exactly the two direct source requests and their order on the successful helper path. They do not yet authenticate a retained graph projection L satisfying `L2 = L0 ++ symbolicLinks a r port`: `ConstraintStore::admit_and_record_provenance` and branch term equality/retention are separately owned and unpinned, and the drain may generate additional constraints. A trace restricted to these direct requests is a possible interpretation, but selecting that restriction and proving its retained order/identity is a remaining correspondence premise; no assumed trace law is used here. Similarly, taking an arbitrary unchanged external inflow I is compatible with R39, but does not prove that I is the graph's actual solver lower storage or newly arrived providers.

Accordingly the exact remaining owners are (1) successful typed-drain/context/effect-application framing for V1 = V0, and (2) the constraint-store/term/direct-request trace projection if a full actual-State.links bridge is required. This is NO_AUTHENTICATED_FULL_PUBLICATION_BRIDGE, with established same-vector PRE interpretation and direct append/copy facts. It is not a discovered representation contradiction, a new semantic restriction, or evidence that the existing R39 theorem is false. Native external contribution generation is separately owned by candidate_effect_contribution (1412–1434); copying a concrete permission never directly calls that constructor.

## Coverage, limits and next action

Commands: synchronous `git show` reads with numbered ranges/searches; Python SHA-256 authentication over all manifest pins; write/hash this one handoff. No executable oracle, seeds, mutations, builds, tests, Lean/checker execution, storage probes, copies/environments, descendants or Git mutations. CPU/RAM were not measured; source lane remained within its 450-second cap. No background process remains. No dirty/quarantined source was read. This is source evidence pending independent review, not an independently checked simulation theorem.

Recommended next action: independently review the same-Vec projection and timestamp equations, apply `prepare_exact` to the derived t0 premises, then authenticate the narrowly missing successful-drain frame/direct-trace owner only if full `constructed_entry_publication` source correspondence needs it. Preserve R111 NO_SAFE_CODE_SLICE, runtime quarantines, R121 consumer indexing and parent soundness/effect-hygiene gates.

## Commit packet

- Exact path: `tasks/agent-loop/inbox/effect-permission-same-pre-r125-source.md` only.
- Baseline: `bf83716eea816536f3cc1d68b323d1567712dd38`; no dependency hash changed.
- Claim/review: bounded static source derivation, full publication bridge conditional, independent review pending; no source-reachable witness refuting it.
- Checks: eleven source hashes and eleven evidence hashes match; focused owner/guard/copy/append/helper/consumer inspection. No execution verification authorized.
- Proposed message: `research: derive same-graph formal entry PRE projection`.
- Primary-only shared deltas: record same-vector PRE Inputs/permissions equation and exact local append, preserve symbolic drain-frame and direct-trace boundaries, and keep later indexed-reader condition separate. Shared records intentionally untouched. Worker stops writing at freeze.
