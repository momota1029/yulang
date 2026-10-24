# Native event correspondence: birth, replay, pairs and equality

Status: frozen research candidate, revision 2; substantive review accepted, provenance correction confirmed.
Outcome class: source-native-evidence and bounded source characterization.
Author: `/root/lean_native_event_audit`; no coauthors or descendants.
Sprint: `LEAN-CORE-CONTROL-BRIDGE-20261024/r2`, assignment source correspondence.
Baseline: `fbbc66cdc63b1f227fff30d33355fc6c35f9dd59` on
`research/simple-sub-intrusion`.

## Objective and governing claim

Trace actual native constructors and consumers against `Contracts.Qualifies`
without changing the original source-scoped A/B obligation. Compiler files are
read-only. The constructive machine theorem belongs to the separate prover
lane; this artifact neither proves nor reviews that theorem.

Authority is the user-selected birth-level rule in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–4 and its exact
supersession in §5; the occurrence identity and definition-root origin in
`notes/design/2026-10-12-intrusion-value-type-association.md`, sections
“Approved extrusion-event qualification” and “Definition-root origin for
nested call-demand extrusion”; and the top-level inference principles §1.1.
The old cross-level F/G qualification is superseded. Same numeric birth does
not identify a lexical scope, telescope, registration component or boundary.
Freshening creates type descriptions, not new source Values or extrusion
occurrences. The birth-level theory note's unreviewed BL5 total-extension
draft is not adopted or used as a premise here.

The fixed original obligations remain `Contracts.lean`:

- `InferenceSoundness` (128): a solution of generated constraints yields an
  original source derivation with `sameScoped`.
- `SourceScopedCoverage` (133): for every supported source derivation and its
  generated constraints, some solution preserves that original scope/witness.
- `PrincipalCoverage` (138): the principal solution has the original instance
  ordering and covers each original derivation in that same scope.
- `NativeCorrespondence` (147): native success realizes generated constraints
  and their solution. `InferenceTermination` is a separate obligation.

`sameScoped` retains rigid imports, one hidden witness, all uses and futures
(Contracts 100–112). Coverage does not require preserving every arbitrary
internal native assignment. `CoreComposition.native_success_elaborates`
(91–106) assumes the native, inference and elaboration obligations; it
discharges none of them. No concrete `SourceProblem` instance was found by
the bounded symbol search in `notes/theory/lean/YulangClosure/*.lean`.

## Actual constructor-to-consumer path

Line locators below refer to the frozen hashes in the inventory.

| Stage | Native owner and observed operation | Evidence limit |
| --- | --- | --- |
| Semantic identities | `candidate_value_graph.rs` `Value`, `Graph::intern`, `Graph::resolved`, `Graph::expression_value` (5–86) | Module/local/parameter/catch/expression identities exist. No Value birth field is retained in `Value`, `Association` or `Graph`. |
| Source origin and receiver | `Graph::retain_source` (87–310) assigns nested initializer ownership to its local definition, resolves Names, and creates one `Association { origin: owners[index], receiver }` for each `Apply`; checking is `ConstraintOccurrenceId(Apply occurrence, 0)`. | This is source Call provenance. It does not enumerate independently sourced non-Apply extrusion associations. |
| References | `retain_source` builds direct owner-to-Name edges plus helper fragments for selected composite values. Helpers have no semantic Value descriptor. | Comments assert full-graph helper path correspondence. No per-birth filtering or per-birth helper compression proof is implemented here. |
| Qualification | `Graph::seal` (312–339) runs SCC over all adjacency; `qualifies` (340–342) compares origin/receiver component IDs. Collection calls `seal` in `lib.rs` 1551; session startup calls it before source level initialization at 10401. | It computes full-graph SCC qualification, not `Contracts.Qualifies` on birth-induced graphs. |
| Levels at source construction | `candidate_source.rs` 1207–1221, 1347–1368, 2258–2267 retain component/parameter levels, increment initializer traversal levels, then initialize mutable native row levels. | Those maps are indexed by type component/parameter positions. No transfer to an immutable semantic-Value birth table is present in the inspected graph/qualification path. |
| Source admission | `candidate_source.rs` 1877–1889 stores Call checking slot 0. `candidate_context_seed` (context 3374–3444) looks that checking up, interns a singleton event set, and records an Origin. | Missing lookup gives `sources = None`; a source constraint occurrence is not automatically an extrusion occurrence. |
| Propagation and replay | `State::relation_with_scoped` (context 3062), `intern_sources`/`union_sources`/`extrusion_sources` (3095–3119), `candidate_context_begin_replay` (3990–4057) retain source sets in relation identity. Replay unions lower/upper source sets. Function ports retain the parent's set (3505–3565). | The set represents ancestry. It carries multiple associations after Replay; it is not by itself a proof of the actual extrusion's unique origin/receiver. |
| Actual polar copies | `candidate_extrude` (extrusion 24–139) allocates one occurrence ID, uses operation-local `(endpoint, polarity, target)` memo keys, returns an existing row when its current level is low enough, otherwise allocates a row and calls `retain_extrusion_parent` before its one-sided link. `finish_candidate_extrusion` is called at 580. | Both Value and Effect row pairs are retained with their actual polarity and target. Immutable Value birth is distinct from this mutable row-level test. |
| Retained occurrence | `Parent` (intrusion 53–61), `retain_extrusion_parent` (305–365), `finish_candidate_extrusion` (368–386) retain raw copy/parent rows, polarity, target, source set, typed comparison and occurrence; groups index the actual returned output. | Initial queueing uses `any(event in sources, references.qualifies(event))`. The native record does not itself supply a source telescope/witness derivation. |
| Reused transformed output | `recapture_candidate_extrusion` (388–420), called from retained-rewrite dispatch in `lib.rs` 14475–14491, indexes by exact comparison and returned endpoint, preserves original pairs, and adds a distinct reuse occurrence/source set. A newly qualifying reuse activates all pairs in that group once. | This is narrower than arbitrary matching row shape. Sound licensing of the reused group by the inherited association set remains a source correspondence premise. |
| Equality | `settle_candidate_intrusion` and `merge_candidate_rows` (intrusion 585–705) canonicalize rows, copy both bound sides with `ParentCopy` transport, retain physical source storage, lower level by minimum, combine non-generic metadata, canonicalize bound provenance, reopen the root, and replay lower bounds against uppers. | Equality changes type-coordinate representation, not source Value references. The code path is not a proof that it preserves the original source conclusion. |
| Publication/use | `prepare_candidate_fresh_use` (scheme 4199–4264) canonicalizes source representatives and uses one per-use row memo; eligible local rows freshen only when current level exceeds boundary and they are not non-generic. `begin_candidate_fresh_bound` (4587–4633) restores bounds through the retained use origin. `candidate_context_fresh_transport_scoped` (context 4278–4292) carries the parent's source set. | A common representative maps to one image within a use. This does not prove original telescope eligibility, witness compatibility across all uses/futures, or whole-domain strategy preservation. FreshUse transport itself does not call `retain_extrusion_parent`; restored comparisons can later cause actual extrusion. |
| Observation | `shadow_apply.rs` 1213–1301 exposes event checking, semantic endpoints/components, pair rows/representatives/polarity/target, groups and reuse source sets. | `same_scc` calls the same native `Graph::qualifies`; it is not an independent oracle. No immutable Value birth or source-law certificate is exposed there. |

## Derivation and exact obstruction

**Bounded source fact, not a whole-language theorem.** For a successfully
retained pair p, let S(p) be the event set read by `retain_extrusion_parent`
at that invocation and Q be native `Graph::qualifies`. Its initial pending
condition is exactly `exists e in S(p), Q(e)`. For a matching unactivated
group reused under S', the recapture path activates the group's complete
`[start,end)` range exactly when S' contains a Q-qualified event, subject to
the explicit same-source/deduplicated-reuse early returns. Settling consumes
each queued pair by `merge_candidate_rows(copy,parent,...)`. This follows by
reading the boolean, pending push/range extension and settle call; it assumes
successful availability checks and makes no claim about all failing executions
or eventual fair draining.

`Contracts.Qualifies` (94–97) instead requires two `LevelPath`s at one level.
Every `LevelPath` constructor checks birth, including its zero-length case.
Neither the SCC traversal nor Q reads any birth assignment. Therefore these
native symbols provide no derivation of the required induced-path premise.
Component/parameter level initialization cannot repair this argument: the
qualification function does not consume those maps and equality later lowers
the row levels. This is a concrete missing constructor/consumer connection,
not a source-qualified counterexample to the approved algorithm. The authority
itself explicitly does not claim birth filtering is already implemented.

Even after supplying birth-level qualification, the following separate
premises are still needed before applying a local diagonal-copy result:

1. **Birth construction and reference projection.** Each semantic Value
   constructor supplies its immutable birth; Name resolution preserves it.
   Helper expansion preserves each induced graph's paths, with all interior
   semantic vertices at the selected birth. Owner: source collection and
   `candidate_value_graph`.
2. **Occurrence licensing.** For each native extrusion/reuse pair group,
   derive the actual source occurrence association through seed, Function
   decomposition, Replay union and FreshUse transport. In particular prove
   that the existentially qualifying member of a unioned event set licenses
   that group's full actual polar pair list. Alternatively the owning source
   derivation must establish an equally strong approved licensing conclusion;
   simply choosing one convenient ancestor is not evidence. Owner:
   `candidate_context` plus `candidate_intrusion`.
3. **Same-cut demand.** Supply an original source derivation/strategy whose
   valuation satisfies the pre-extrusion demand at the actual cut. Row bounds
   and the fact that a native comparison ran do not establish this source
   hypothesis. Owner: original source constraint-generation proof.
4. **Scope and publication/use transport.** Construct the required solution
   with the original lexical package, rigid imports and shared witness over
   every lawful input/use/future, and show allocation and evidence transport
   preserve the added equalities. Same-birth SCC membership and the per-use
   canonical-row memo do not establish this. Owner: source generalization /
   capture / FreshUse proof, with actual native maps.
5. **Native realization.** Interpret all retained clauses, canonicalization,
   replay and successful publication as the original generated solution; prove
   native success at the owning observation boundary. Owner: native bridge.

With those premises established independently at their owners, a local
same-cut extrusion result can be applied to actual pairs and transported to
the source-scoped conclusion. This sentence is a conditional application plan,
not a new proved theorem. No total-extension draft, equal-endpoint shortcut,
arbitrary-model preservation demand or narrowed source domain replaces those
premises. The first concrete construction missing from native correspondence
is item 1; items 2–5 remain open even if it is supplied.

## Evidence independence, coverage and resources

The comparison is static: authoritative rule and Lean proposition versus
actual Rust producers/consumers. The native observation API shares the native
qualifier, forests and source-set implementation; agreement with that API
would be internal consistency, not an independent semantic oracle. No checker
that assumes Replay or extrusion rules was used. No seeds, randomized ranges,
mutations, executable experiments, Cargo, Lean builds, tests, network calls or
descendants were run. No new source-qualified counterexample was found by this
bounded audit. The old nested F/G and odd/even attacks were not rerun.

Coverage is the listed static source slices and bounded Lean symbol search.
All-syntax source admission, every non-Call extrusion, failures/rollback,
dynamic late SCC updates, complete retained-clause semantics, native execution,
full Call/effect/handler behavior and whole-domain strategy preservation were
not established. No production promotion follows. Any dependency mismatch,
source change, unaccounted path, or required source meaning change invalidates
the affected correspondence and returns it to the primary.

Grant: 600 wall seconds, zero build/test/probe processes. First observed clock
was `2026-10-24 13:53:22 UTC`; final timing and frozen artifact hashes are in
the handoff. Actual CPU and peak memory were not measured. Requested Sol/high;
observed routing/model/effort UNKNOWN. Only short read/hash commands and the
two leased Markdown writes were used. Independent review of revision 1 found
only the stale contract provenance corrected in revision 2; technical claims
remain accepted as bounded evidence.

Recommended next action: primary assigns an owner to derive immutable birth
and per-birth semantic-path correspondence at `Graph::retain_source`/`seal`/
`qualifies`, then checks that evidence at the retained-pair activation seam.
Keep original source/native and A/B parents OPEN while the independent Lean
machine bridge proceeds.

## Frozen direct evidence inventory

All five Rust inputs and the birth-level design/theory inputs pinned by the
contract match their pinned hashes. Additional read dependencies below are recorded
explicitly; the unreviewed birth-level theory note was read for status only.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/lean-core-control-bridge-20261024-r2.md` | `806357d7c2b5cf9f4152904cf8fc085fe90add3ab5c644ac592dab30b062b681` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |

## Commit packet

Exact leased paths: this artifact and
`tasks/agent-loop/inbox/20261024-lean-native-event-correspondence.md`.
Baseline SHA: `fbbc66cdc63b1f227fff30d33355fc6c35f9dd59`.
Changed dependency hashes: none observed; additional read dependencies are
inventoried above. Review: accepted bounded static evidence; no source-qualified
counterexample. Checks already
run: bounded `rg`/`sed`/`cat` source inspection, `git rev-parse HEAD`,
`sha256sum`, and a read-only Python 3 inventory comparison against baseline
Git blobs (all 16 current hashes and all 15 non-contract baseline bytes match).
The first inventory invocation used unavailable `python` (exit 127); the
unchanged script succeeded with `python3` (exit 0). No execution proof occurred.
Proposed commit message: `research: map native extrusion provenance to birth-level obligations`.
Shared-record deltas intentionally left to primary/curator: record this frozen
source correspondence result, retain native/A-B parents OPEN, assign the exact
birth/path and occurrence-licensing premises, and obtain fresh review. No shared
record, compiler, manifest, expected output, question bundle or other lease was
written. Revision 1's independent review found only stale r1 provenance;
revision 2 corrects it to r2 without changing technical claims.

Revision 2 corrects sprint provenance after independent review found the
revision 1 header still named the superseded r1 contract. The source findings
and all technical claims are unchanged. Reviewer confirmed the r1 content was
bounded and accurate and the corrected r2 metadata.
