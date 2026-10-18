# R47 temporal copy refinement: fixture reachability obstruction

Status: frozen candidate static source/native derivation; independent review pending.
Assignment: `R47-SOL-TEMPORAL-PROOF`, handoff revision 1.
Author: `/root/r47_temporal_copy_proof`; no coauthors or descendants.
Contract: `temporal-copy-evidence-20261019-r47`, revision 1,
SHA-256 `aba8009c8ec658af48ed2844e6a9c9b4554b4343ada19f8a7aae85b978574131`.
Grant HEAD: `e39d3c8d5` (parent-supplied, no Git command used).
Source baseline: `3860c5d2bac12efde6fb543ba68a637ef47a9ab2`.

## Result and parent application

**FIXTURE_UNREACHABLE:** in the pinned implementation, every successful ordinary
helper `LocalFreshRoute` in `active_outer_root_two_helper_uses` is reconstructed
immediately after its own capture. Capture deduplicates by the then-current
representative; no operation between capture and the reconstruction row loop
merges those representatives. Consequently every row recorded by that loop has
`canonical_rows_hit=false`. The requested authentic later hit with
`image == existing_image != source_representative` cannot be produced by these
helper routes. This is a static path argument, not an observed execution or a
source-qualified counterexample to inference correctness.

**MISSING_RETAINED_EVIDENCE:** independently, the retained baseline observations
do not authenticate representative evolution from reconstruction through later
bound restoration, source actions, intrusion settlement and rollback to final
inspection. This is an evidence obstruction for that later temporal edge. Adding
observations alone cannot resolve the earlier fixture reachability obstruction.

Applied to R37, the original native transport prerequisite remains unsatisfied:
there is no actual later canonical-map-hit witness for the scoped Apply/helper
join, and the join's historical-to-inspection edge is unsupported. The result
removes this fixture as evidence for that prerequisite; it does not refute the
transport theorem universally. The full inference/evaluator theorem and original
Simple-sub A/B remain **OPEN, 0 -> 0**, preserving the accepted source domain,
recursive worlds, both frames, aliases, arbitrary W, complete Call/effects,
F1 and FK1 as distinct quantifiers, N-Transport, soundness, principality and
termination. No `Desc`, ordered `D_q`, typed `CopyScope(C/D)`, result-description
owner, or typed publication is constructed. R46's ordinary Application
output-formation obstruction remains at its original owner.

## Exact identities and owner evidence

The contract's graph-row owner is named `Capture::row` in these source bytes
(`candidate_scheme.rs:749`), rather than a literal `GraphBuilder` type.

| Phase | Meaning | Actual owner and retained evidence |
| --- | --- | --- |
| Capture request | Raw requested key K | `Capture::row`: local `requested`; retained in `CapturedRowObservation` only on first insertion. A dedup hit returns early and retains no separate request occurrence. |
| Capture representative | C = rep at capture of K | Same owner stores `Row.key=C`, observation representative C, graph index, level, non-generic flag, boundary and local flag. |
| Reconstruction source | S_i = rep at reconstruction of captured C_i | `prepare_candidate_fresh_use`, `:1580-1613`, samples and stores S_i before image selection. |
| Canonical map first entry | Earliest row j whose reconstruction source is S_i | Local `canonical_rows`; observation `first_entry_graph_row` finds the first prior observation with that source. This map is new for every preparation. |
| Image | Raw row identity I_i placed in `FreshUse.rows[i]` | Same loop records `existing_image`, hit/allocation flags and image. A hit copies the earlier map value without allocating. |
| Retained route | Graph, row vector and reconstruction observations for one source use | `GraphState::commit_local_use`, `:654-684`, transfers the completed frame's graph and fresh-use records; route identity is per source occurrence. |
| Later representative | rep at inspection of any retained raw key | `candidate_intrusion::State::rep`, `:115`; reports current forest only. It supplies no historical timestamp or merge path. |

These are raw identity relations at particular times. A fresh raw image differing
from S_i does not assert that their representatives remain different later.
The two helper routes have separate captures/preparations; their final images
need not be unequal. The canonical map is not shared between those routes.

## Owner-derived reconstruction relation

For one successful invocation, let C_i be graph row i, S_i its sampled source,
M the canonical map, and G_i the recorded freshening guard:

```text
G_i = row.local && level(S_i) > graph.boundary && !non_generic(S_i)
```

The loop implements exactly these three cases:

1. If M already contains S_i, let j be its first-entry row. Then j < i,
   `existing_image=Some(I_j)`, `I_i=I_j`, hit=true, allocation=false.
2. Otherwise, if G_i holds, allocate a fresh row F of the same component kind,
   set I_i=F, insert M[S_i]=F, hit=false, allocation=true.
3. Otherwise set I_i=S_i, insert M[S_i]=S_i, hit=false, allocation=false.

No forest union occurs within this row loop. Hence a genuine recorded hit whose
first entry allocated fresh would establish the requested raw-key relation:
I_i = existing_image = I_j, and I_j != S_j = S_i. The distinct fresh ordinal
comes from `fresh_value_at_level` / `fresh_effect_at_level`
(`lib.rs:10243/10274`), which append bounds and synchronized metadata. This is a
conditional operational derivation from actual branches. Its missing premise
is an actual reachable hit, not an additional mathematical identity law.

### Why this fixture cannot provide that premise

Fix any successful fresh helper route; the argument applies independently to
each of the selected literal helper uses and to both C/D coordinates.

1. `route_candidate_local_run` executes
   `capture_candidate_graph_owned(root,boundary,frontier)` at `:2022`, then
   `prepare_candidate_fresh_use(&graph,level,caller)` at `:2024`. The intervening
   operation is a caller-region lookup. No source action or solver drain runs.
2. `capture_candidate_graph_inner`, `:1207-1344`, builds `Capture` with immutable
   session access. Throughout row discovery its representative forest is fixed.
   `Capture::row` canonicalizes a request and returns an existing index if its
   canonical key is already present. Therefore all inserted C_i are pairwise
   distinct roots in that forest, including keys outside the forest whose
   representative function returns the key unchanged.
3. Capture's mutable wrapper performs scope ownership/resource accounting and
   failure checks. Preparation before its row loop performs context-use and
   scope-remap allocation, scratch allocation and resource accounting. None
   calls intrusion settlement, compression, merge or rollback. The resource
   sampler reads `state.intrusion.bytes()` through an immutable state borrow
   (`lib.rs:10547-10780`). Context and scope operations borrow their respective
   subfields and cannot mutate the separate private representative forests.
4. During the row loop fresh allocation appends new row storage; it changes no
   existing representative. Forest initialization in
   `retain_extrusion_parent` (`candidate_intrusion.rs:264-282`) also only extends
   with identity roots, and is not invoked by this row-allocation loop. Thus
   S_i=C_i for every i, and the S_i are pairwise distinct throughout the loop.
5. Inductively, before row i, dom(M)={C_0,...,C_(i-1)}. Since C_i is distinct
   from every earlier key, M.get(C_i) is None. The loop records hit=false and
   first-entry=i. This proves the invariant for all inserted rows.
6. Only after preparation returns does `step_candidate_local_use`, `:2151`,
   restore bounds and admit the final link. Those operations can drain/merge,
   but cannot retroactively change immutable recorded hit flags. On success,
   commit transfers those same observations. A fresh capture for another
   helper use repeats the deduplication and starts a new empty canonical map.

The invariant is stronger than the R37 selector criticism: it does not assume
that the final join succeeds or that its all-row current-state checks hold.
It applies to the actual creation path of every successful ordinary helper
route under the pinned source bytes.

Exact falsifier: show an authentic owner call on this same path that changes
the representative equivalence of two inserted graph keys after capture and
before/during the row loop, or show that a helper route reuses an older graph
instead of executing `:2022`. A synthetic observation, final equivalence class,
different graph consumer, or manually separated capture/reconstruction does
not falsify this path claim. Such another path needs its own reachability
evidence and Luna's contract decision before being used as the R47 witness.

## Later merges, rollback, and the absent temporal edge

`execute_candidate_action` (`candidate_source.rs:1658-1694`) admits Candidate,
Link and Local actions. Local restoration and the final link call real solving
consumers. `lib.rs:12136` and `:12372` settle pending intrusion when the typed
worklist is empty. Thus reconstruction need not be the final representative
state.

`merge_candidate_rows` (`candidate_intrusion.rs:520-615`) canonicalizes the
retained copy and parent. On unequal same-kind roots it transfers both bound
sides and origins, combines levels by min and non-generic flags by OR, updates
the copy root's forest parent (`:593/600`), canonicalizes context bounds,
increments generation (`:603`) and replays dependent bounds. Compression
(`compress_candidate_forests`, `:436`) rewrites forest links while preserving
the current equivalence relation. These are distinct from capture and image
selection; a final `rep` lookup cannot identify which happened when.

`State::begin` retains rollback lengths, generation and other state.
Union/compression writes retain old links in `Undo.forests` when a route journal
is active. `State::rollback`, `:145-180`, restores old links in reverse order,
truncates newly born rows and provenance, restores pending/activation state and
generation. `rollback_route_transaction` (`lib.rs:9435`, especially `:9470-9490`)
also restores source/local continuation ownership and removes routes born in
the failed transaction. Commit releases `journal.intrusion` (`lib.rs:9304`).
The undo journal is therefore rollback machinery, not a retained complete
forward transition history available to the final test join.

For a future fixture, the needed relation has the form

```text
K --capture at t_c--> C --reconstruct at t_r--> S
  --authenticated surviving merge/rollback history to t_f--> rep at t_f(K/C/S)
```

The source field must continue to mean rep at t_r(C); it must not be overwritten
with rep at t_f(C). A later lawful union can change the latter. Rollback may
restore an older representative and generation; equality of generation alone
therefore proves neither interval stability nor absence of intermediate writes.
Numeric identities born in an aborted transaction also require surviving
allocation/route ownership before reuse can be interpreted as the same object.

**Exact missing owner/premise:** `prepare_candidate_fresh_use`'s
`ReconstructedRowObservation` retains S without an authenticated transition
position, and `merge_candidate_rows`, compression and `State::rollback` retain
no surviving ordered observation history connecting that position to the
inspection in `captured_source_matches` / `join_apply_pair_capture`. At the
pinned bytes this is `MISSING_RETAINED_EVIDENCE`. This conclusion is about
evidence for the test's identity claim; it imposes no new general rollback
requirement on inference semantics.

## Prior work reused and rejected

R37 revision 3's closeout is reused for indexed Parent authentication, signed
C/D coordinates, exact Apply occurrence/event, structural trigger and negative
substitution intent. Its two blockers remain valid. In particular,
`captured_source_matches`, `:2236-2247`, equates historical S with current rep
for every row, and `join_apply_pair_capture`, `:2348-2352`, selects `.position`
in the final canonical class. Conditional on those all-row checks passing,
the earliest selected row is also the first entry for its reconstruction
source, so the join's hit arm cannot witness a later row. The downstream
`if canonical_rows_hit` assertions (`:2735`) assert no existential hit.

The integration fixture (`candidate_local_self_recursion.rs:105-138`) checks
two FreshUse routes, component kinds, active-root behavior and export. Those
checks do not establish any canonical hit. No success is inferred from their
presence or from the fixture's call count. R46 is reused only for its recorded
bounded ordinary-Application formation obstruction; its source occurrence map
does not supply the missing `Desc` or the native hit witness.

## Exact frozen dependencies

All nine contract dependencies were hashed at intake; source files were hashed
again before this write and still matched. Existing sources are primary-owned
inputs; their historical individual authors are UNKNOWN. This artifact's
derivation and counterexample method are authored only by this worker.

| Path | SHA-256 |
| --- | --- |
| `notes/progress/2026-10-18-r37-rev3-review-closeout.md` | `5c1aa3ea9f653a73d5f7466f61f9cbc32bc641fcc56ac5eeed6ff3da201f1d44` |
| `tasks/agent-loop/sprints/authentic-apply-copy-bridge-20261018-r37-rev3.md` | `b19c4131f79476f787b8ef424e46f38a396598234dab5400215025938bd0d250` |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |
| `notes/progress/2026-10-19-r46-closeout.md` | `b39e5957cf85d23020163319613a77deb1a5db1a63ece71eeaa481d11d5f0a72` |

Governing evidence: `rules/goal-driven-sprints.md`
`e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a`;
`tasks/agent-loop/README.md`
`1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf`;
`rules/design-authority.md`
`e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`;
top-level inference principles
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
2026-10-16 sprint decision
`2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`.

## Checks, resources, mutual TODOs, stop

Checks: read-only owner inspection using `rg`/`sed`/`cat`; SHA-256 checks above.
No compiler/source edits, tests, Cargo/builds, executable transition probes,
Git, external contact, scratch files or descendants. The only new paths are
this artifact and `tasks/agent-loop/inbox/20261019-r47-proof.md`.

Requested model/effort: Sol/high. Observed model/effort: UNKNOWN/UNKNOWN; no
runtime metadata established either. Resource cap: 900 seconds, fully charged
on grant; CPU/RSS UNKNOWN. First clock observation: 2026-10-18 16:04:43 UTC;
pre-write clock: 16:07:02 UTC. These clocks bound part of the activity, not the
grant time or a refund. No unused grant is reclaimed here.

`R47-TODO-REACHABILITY` to Luna: adjudicate this exact no-hit owner argument
before further witness implementation. Inputs are the frozen owners above;
falsifier is an authentic intervening union or older-graph helper route.
Output is a reviewed reachability decision. A different fixture, constructor
schedule or graph consumer requires Luna's authority/dependency decision; no
semantic change is proposed by this artifact.

`R47-TODO-TEMPORAL` to Luna's source/native observation owner: for any future
reachable witness retain or independently establish the reconstruction-to-final
representative edge across merge/compression and rollback, with surviving
route/allocation ownership. The first missing evidence is at
`ReconstructedRowObservation` plus `merge_candidate_rows` / `State::rollback`;
the consuming symbols are `captured_source_matches` and
`join_apply_pair_capture`. Falsifier: a valid intervening merge/rollback history
that the proposed owner record cannot distinguish, a forged record accepted,
or a hit asserted without a distinct earlier first entry. This TODO grants no
additional implementation path or resource.

Next step belongs to Luna: fresh independent review of this frozen static
obstruction and contract adjudication. This worker cannot certify the combined
result. Stop condition reached: fixture obstruction and exact missing temporal
evidence. **WRITES_STOPPED; NO_DESCENDANTS** after the assignment inbox is frozen.
