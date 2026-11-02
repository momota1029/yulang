# R230 native owner correspondence — revision 1

Sprint-ID: R230; admitted contract revision 1, SHA-256
`38139890a715aa7c11a8a788d04ee442696c7755a38c7401988ad6201d3d5ef3`.
Assignment-ID: R230-OWNER; handoff revision 1.
Outcome class: **source-native-evidence**, static and bounded to two native owners;
**NO_SAFE_CODE_SLICE**. This is a producer report, pending independent review.

## Objective, authority and baseline

Compare R230's query-computed roots, owner-local capture and per-use valuation
with the actual native capture/reconstruction/publication consumers. The governing
contract sections are “Original parent and success evidence,” “Fixed dependencies
and exact outputs,” lane 2 in “Lanes, resources and verification,” and “Review,
parent application and stop conditions.” Preserve the selected structural model:
all four Function coordinates are retained; no new independent effect-port
comparison is asserted as language semantics.

Unchanged original parents: `SourceProblem.SourceScopedCoverage` and
`SourceProblem.PrincipalCoverage`, `YulangClosure/Contracts.lean`, as identified
by the contract. This audit neither reads nor proves those definitions. Parent
delta **0**; roots **0/4**; packages **0/5**. No native simulation, original source
witness, soundness, principality, termination or production promotion follows.

Baseline HEAD authenticated twice as
`9137e14caa418cd3f686fc892b9cea9502a70b5f`.

| Frozen dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `AbstractUpperInsertionInvariantR229.lean` | `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a` |
| `AbstractBoundCycleNormalizationR223.lean` | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |

Lean dependency paths are under `notes/theory/lean/YulangClosure/`. Their bytes
were hashed only; no Lean module was inspected or executed in this assignment.
No dependency hash changed. Rust reads were restricted to the two listed owners.
Rules read: root `AGENTS.md` and `AGENTS.pre-sprint.md`, research-lab and its
preserved baseline, design-authority, git-concurrency, goal-driven-sprints, the
top-level inference principles, sprint skill and current-state/handoff protocol.
No child team or sprint admission was initiated.

Worker: `/root/r230_owner`, sole author; no descendants. Launch authority is the
parent's R230 assignment message. Current session and effective model/effort are
UNKNOWN from this worker's runtime metadata; no model execution is inferred
from configuration. Exact write lease: this file only.

## Positive correspondence and exact native locators

All line locators refer to the frozen Rust bytes above.

1. **Construction and boundary.** `candidate_source.rs:1356` and `:1371`
   schedule binding initializers at `level + 1`, with installation at the
   enclosing boundary. `:1547` records a local region and begins capture;
   `:1562` emits initializer effects once into the enclosing computation and
   schedules `Install` or `LocalAnnotation`. `:2292` installs planned component
   and parameter levels. This supplies concrete native boundary inputs, not
   an established R229 metadata invariant.
2. **Native root and reachability.** `candidate_scheme.rs:2890` seeds
   `Graph.root` from one positive `ValueRow(row)`; `Graph.live_root` and
   `boundary` are stored at `:2868`. `:2940` drains pending structural nodes
   and discovered rows. `:1988` interns rows by current intrusion representative
   and sets `local = level > boundary && !non_generic` at `:2012`.
   `:2400` stops bound traversal at inactive rows; `:2411` and `:2452` traverse
   value/effect direct lower/upper and exact structural bounds for active rows.
   Bound owner orientation and evidence are retained at `:2351`.
3. **Complete structural coordinates.** `candidate_scheme.rs:2226` captures
   Function children in `[argument, argument_effect, result_effect, result]`
   order, with kinds `[Value, Effect, Effect, Value]` and polarities
   `[opposite, opposite, p, p]`. Reconstruction at `:4765` uses that same
   four-element order. Variant tags and ordered payloads are copied at `:2282`
   and `:4783`; record field metadata is copied via `field.map` and its value
   replaced at `:2305` and `:4816`; tuple positions are retained at `:2321`
   and `:4834`. The definition of `RecordField::map` is outside this read lease,
   so preservation of labels/optional flags rests on that imported operation's
   contract, not a new independent audit of its implementation.
4. **One map within each use.** `candidate_scheme.rs:4529` starts one
   `context_use` and builds one `FreshUse.rows` vector; all row terms use this
   vector at `:4761`. The same vector maps role subjects (`:4544`), FieldTail
   interfaces (`:4549`) and registered Function argument-effect incidences
   (`:4614`). `FreshUse` retains terms, effect operands, scope/context/evidence
   remaps (`:782`); `into_retained_parts` keeps these maps (`:816`). This is
   concrete alias-sharing data, not yet a semantic valuation theorem.
5. **Shared inactive identities.** `candidate_scheme.rs:4581` re-resolves each
   captured row to its current representative. For a first encountered
   representative it allocates a fresh row of the same kind exactly when both
   stored capture-locality and live eligibility hold (`:4591`); otherwise it
   uses the source representative itself (`:4593`). Later equal representatives
   reuse the first image (`:4589`). `:2405` explicitly explains that inactive
   bounds remain live in the session so later constraints reach shared anchors.
   Separate uses have distinct context origins even when sharing an older row
   (`:4974`).
6. **Actual consumers.** `candidate_source.rs:2415` installs the exposed local
   term after a `PublishLocal` stage; `:2441` obtains it from the initializer,
   and `:2446` from the annotation constructor. Installation stores a root row,
   boundary and optional region, not a frozen generalized graph
   (`candidate_scheme.rs:5096`). Each later local occurrence recaptures that
   live root and creates one fresh use (`:5271`, `:5300`). `:5430` restores all
   captured bounds before admitting the reconstructed root into the occurrence
   component (`:5446`). `:1680` retains the exact graph and maps in the committed
   local route. Definitions similarly recapture at each incoming use (`:4441`),
   restore bounds before returning the fresh root (`:4508`), route that root to
   the receiving component (`:4995`, `:5043`) and retain the maps (`:5053`).
   Top-level member graphs are staged before visibility (`:3209`, `:3225`,
   `:3281`); this is publication ordering evidence, not atomicity proof of every
   imported fallible operation.

## Explicit static derivation

Fix one successful call of `prepare_candidate_fresh_use`, and assume its imported
representative lookup and fresh allocators satisfy their contracts, the graph
indices are valid, and the live representative/metadata state is unchanged except
for fresh allocation during this row loop. For captured position `i`, write
`r_i = rep(row_i.key)` and
`E_i = row_i.local && level(r_i) > boundary && !non_generic(r_i)`.

From `:4581`–`:4613`, induction on loop position gives:

- On the first occurrence of representative `r`, its image is a fresh row of
  the same kind if `E_i`, and is `r` otherwise.
- On every later occurrence of `r`, the hash-map hit returns that same image
  before evaluating the later occurrence's eligibility branch.
- Thus equal source representatives have equal images within one use. For two
  successful calls with unchanged representative `r` and inactive first
  occurrences, both images are literally `r`. This derives conditional anchor
  identity sharing across uses.
- Reconstruction of `Node::Row` uses precisely that image. For structurally
  well-founded graph children, each Function/record/tuple/variant coordinate is
  rebuilt from the same row map, by inspection of the reconstruction cases.

This derivation establishes operational map sharing under explicit premises.
It does not establish a `Sol` valuation, either direction of solution transport,
mutual structural `Sub`, or any whole-source property. In particular,
first-image reuse does not establish that `E_i` is uniform across graph rows
which later merge to the same representative. That requires an independent
metadata/representative invariant or a proof that the first-image choice is
adequate. No reachable violation is claimed here.

## Negative correspondence and first missing premise

**First missing native application premise:** establish a relation from the live
source-generated native state at each capture/use to an actual R229 history
from `CoreProblem.initial`, including its bounds, levels/non-generic metadata,
representatives and the selected query/interface coordinates. Neither inspected
owner exports or verifies such a relation. `candidate_source.rs:2469` dispatches
many owners beyond upper insertion: facts, annotations, lambdas, formal-effect
equality, operations and catches. `candidate_scheme.rs:4947` restores both kinds
and both stored bound orientations through an imported replay/admission owner.
The correctness of these callees is outside this audit. Therefore successful
native publication cannot be identified with R229 successful-upper-only history
merely because this code has capture and fresh-use maps.

Specific additional gaps, after that premise:

- **Roots are not identical objects.** Native code does not compute the free
  variables of an arbitrary queried structural term. It begins at a positive
  value row and augments the capture frontier with role subjects (`:2894`),
  FieldTail value/effect interfaces and case guards (`:2904`), explicit member
  interface roots (`:2925`), latent negative Function demand roots (`:2960`)
  and evidence payload tails (`:2967`). Reachability and successful index
  lookups demonstrate coverage of this native graph, not equality with R230's
  query-variable root set. The context variable named `roots` at `:4696`
  contains relation contexts, not query type variables.
- **Two SCC notions must stay separate.** Definition SCC orchestration at
  `candidate_scheme.rs:3150`–`:3206` concerns definition dependencies and source
  regions. It is not evidence of uniform eligibility in a variable-bound SCC.
  The capture/fresh-use entrypoints use local level/metadata checks; no
  history-derived bound-SCC closure certificate is constructed there.
- **Live representatives can change.** Capture canonicalizes rows (`:1991`),
  while fresh use canonicalizes them again (`:4584`) and tests both stored
  locality and live metadata. R230's abstract quotient/valuation cannot simply
  be substituted for this two-time map. Preserve R229's known native
  representative-change differences. Equal representatives share one image,
  but the first row wins if their stored-local eligibility differs.
- **Self-pair elision remains a known difference.** The assignment carries
  R229's prior native self-pair-elision finding. Its insertion owner is outside
  the two allowed reads, so this report preserves it as inherited evidence,
  without claiming to reverify its implementation locator. The capture owner
  only traverses already stored bounds. An abstract self-cycle application
  therefore does not demonstrate that the same self-edge is stored natively.
- **Native effects include additional evidence.** Effect operands, scoped
  relations, latent demands and scope/context remaps (`:4666`, `:4859`,
  `candidate_source.rs:274`, `:296`) carry information absent from a bare
  structural row valuation. Source-region copying has private experiment
  limits (`candidate_source.rs:194`, `:305`); it is not type-root computation
  or a whole-language support boundary.
- **Consumer success is one operational direction.** Restoring captured bounds
  and routing a fresh root does not prove the converse solution transport or
  principal factorization of all original source derivations. No source
  `sameScoped` witness is retained or established by the inspected path.

`NO_SAFE_CODE_SLICE` follows from both inspected owners: the source scheduler
supplies native roots/boundaries through many imported semantic operations, and
the scheme owner captures/replays live representatives, augmented roots and
evidence. A compiler change based only on R230 would assume their missing
simulation and consumer premises. The admitted contract authorizes no Rust
change; no implementation was attempted.

## Checks, coverage, resources and next action

Commands run: bounded `cat`/`sed`/`nl` reads of the required operating documents
and admitted contract; targeted `rg -n` over the two Rust owners; `sha256sum`
of the contract, both owners and four pinned Lean dependencies; read-only
`git rev-parse HEAD`; and `git diff --numstat --` the two owners (empty output).
All completed successfully. Contract/owner hashes and HEAD were authenticated
again immediately before writing. No Rust/Cargo/tests, Lean/Lake/build, executable
experiment, mutation, randomized search, benchmark, scratch file, Git mutation,
network access or child process team was used. Seeds/ranges: not applicable.

Oracle independence: source inspection is grounded in the pinned implementation
and independent of a toy checker, but it shares imported type/allocator/replay
contracts and is not independent review of the proof. Coverage is the listed
native entrypoints/cases, not exhaustive source generation, imported callee
correctness, error recovery/rollback, all annotation/effect cases or the new
R230 proof artifact. No proof artifact was consumed. Fail conditions for applying
the derivation include dependency drift, invalid graph indices, broken allocator
contracts, unaccounted representative/metadata changes, or unsupported effect
evidence; they are unresolved obligations rather than observed failures.

Budget: one read-only research worker, at most four lightweight command calls in
an independent-read batch, no heavy process and zero cache growth. Wall-time budget 900 seconds;
exact cumulative CPU/RSS and dispatch start timestamp are UNKNOWN. Work completed
within this assignment's active turn without a timeout. Hashing/read commands
were subsecond in reported tool wall times; no performance claim follows.

Recommended next action: after reviewing R230's abstract result, have Luna admit
one exact native correspondence packet at the bound admission/representative
owner, proving the live capture/use state relation above or producing a reachable
counterexample. Do not create another assumed structural publication checker.
Proposed stable TODO: `R230-NATIVE-HISTORY-QUERY-1`; inputs are the frozen R230/R229
theorems plus these owner hashes, output is a native history/query translation
with alias/metadata invariants or a source-qualified failing trace. It requires
a new read/write lease if it crosses the current two-owner boundary.

Shared-record deltas for Luna/curator: record this native bridge OPEN, keep
`NO_SAFE_CODE_SLICE`, parent delta 0, roots 0/4 and packages 0/5; keep R229's
self-pair/representative exclusions. No shared record was changed here.

## Frozen handoff and commit packet

Worker state: complete; **writes stopped on submission of revision 1**; no
descendants, generated outputs or unresolved descendant leases. This frozen
revision is immutable pending primary acknowledgement and independent review.
Artifact SHA-256 is supplied in the accompanying submission, avoiding a
self-referential in-file hash.

- Exact leased/changed path:
  `tasks/agent-loop/inbox/abstract-upper-publication-factorization-r230-owner.md`.
- Baseline SHA: `9137e14caa418cd3f686fc892b9cea9502a70b5f`.
- Changed dependency hashes: none; direct dependency hashes are recorded above.
- Claim/review status: bounded static source-native evidence, pending fresh
  independent review; no theorem closure or production authority claimed.
- Checks already run: focused reads, hash authentication, baseline authentication,
  empty source-owner diff; no builds/tests or executable probes.
- Proposed research-checkpoint commit message:
  `research: record R230 native publication correspondence limits`.
- Shared-record deltas intentionally left for primary/curator: the OPEN native
  history/query bridge and unchanged parent counters/exclusions listed above.
