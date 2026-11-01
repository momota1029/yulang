# R144 scope transformer source/proof bridge — frozen revision 1

Sprint: `EFFECT-PERMISSION-SCOPE-TRANSFORMER-SOURCE-BRIDGE/20261102-R144`.
Contract SHA-256: `e50116b928501c40eabe6d33dfe1c4e7579a5b557f7a20a3adf67458878b95d5`.
Assignment/author: `/root/r144_scope_bridge`; session `R144-SCOPE-TRANSFORMER-SOURCE-BRIDGE`; actual launch acknowledged by primary packet. Requested/observed model and effort: UNKNOWN. No descendants.
Baseline: `77cf25096f8271590b89380fc988d7e2dd11e7d6`.
Exact write lease and sole changed path: `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-proof.md`.
Outcome class: source/native evidence plus a conditional finite-support derivation; no new Lean theorem, executable experiment, implementation certification, or parent closure.

## Inputs and authority

Initial read-only `sha256sum` matched every admitted frozen input:

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `notes/design/2026-10-15-compose-scoped-effect-release.md` | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| `notes/progress/2026-10-26-whole-metatheory.md` | `242015bcca9ca9bb5bff038f26755a13dcc6defb555505b40be4a6b854392d43` |
| `notes/theory/2026-10-15-compose-scoped-release-construction.md` | `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e` |

Governing sections: compose design “Direct decision”, “Scope of the operation”, “Implementation direction and remaining work”; whole-metatheory §2; construction note §§1–2; top-level inference principles §§1–5. Read root operating maps, research-lab rules (including preserved baseline), design-authority, Git concurrency, goal-driven sprint rules and relevant proof skills. The accepted `'e?` operation releases the selected protection also within `'f`, retains contributions/attribution, and preserves independent scopes. It grants no capture. No language meaning is selected here.

The implementation lane may subsequently append tests to `candidate_scope.rs`. All source locators below describe the admitted bytes, not that lane's moving candidate. The primary must bind review to its final source snapshot; this handoff does not certify that candidate.

## Exact formal surface and Rust content

All declaration names below are under `YulangClosure.NativeScopeTransformer`.

`evaluate_then` (Lean line 188) quantifies over **every** `first second : Transformer` and `initial : State`, with no injection/safety/source-typing premise, and concludes membership equivalence of `(first.then second).evaluate initial` and `second.evaluate (first.evaluate initial)`. `Equivalent` compares input and protection membership, not list equality. `evaluate_protection` (143) exposes the content equation:

```
I' = I union J
s in P' iff (keep_s and s in P) or exists t in M_s, t not in I
```

Rust `evaluate` (180–209) sorts/deduplicates its incoming vectors before binary searches; `then` (134–175) merges canonical vectors. Its keep bit is `keep2 && keep1`; it retains the first missing tags only if `keep2`, and filters second missing tags against first stamps. Thus its displayed formula matches Lean `composeEntry` (98–106), whose append/filter representation is interpreted by membership. This is a formula-level correspondence argument, conditional on Rust loops implementing those set operations; it is not a verified refinement of sorted vectors, fallible allocation, or Rust execution.

`evaluate_rename` (408) quantifies over arbitrary transformer/state and **one shared** `scopes tags : Nat → Nat`, requires `Function.Injective scopes` and `Function.Injective tags`, and concludes evaluation/renaming membership equivalence. Rust `remap` (214–265) accepts stateful closures, evaluates the input closure once for each distinct stamp/guard ID and the scope closure once per canonical entry, stores images, rejects duplicate images separately in each coordinate, then sorts. It checks only transformer support. It neither renames an incoming state nor establishes a global function, shared-use consistency, or injection against IDs outside that support. Scope and input IDs are different sorts; cross-sort equality is irrelevant.

No checker or axiom audit ran in this packet. These are inspected declarations in the existing module, not fresh kernel-check receipts. The existing generic `witness_observer_preserved` (334) preserves a supplied complete witness by definition; Rust's two-coordinate kernel does not construct that witness.

## Construction and consumers

| Native path in admitted files | Relevant laws and established source fact | Remaining application premise |
| --- | --- | --- |
| `candidate_source.rs:1212`, `155–170`, `1869–1916` | Visiting an expression allocates a computation scope; an Apply records callee/argument/result and effect endpoints. Call index becomes its input-route ID and is retained in the occurrence's source region. | Authentic traversal/Call constraints for all supported forms, not merely these retained fields. |
| `candidate_context.rs:3803–3835`, seed slot 0 | With scoping enabled and a retained introduction, `ScopedDemand` carries that call index, introduction root, computation scope and input ID together. | The introduction and numeric local slot must correspond to the intended source Call across the full caller chain. |
| `candidate_context.rs:3930–3989`, Function decomposition | Parent root must match demand root and parent transformer must be zero. ArgumentEffect gets `stamp_input(demand.input)`; ResultEffect gets `protect_body(demand.output_scope, demand.input)`; value ports get identity. Demand is cleared on all four children. | Actual propagation of one contribution through the right ports; algebra alone cannot infer such routing from effect-family/type equality. |
| `candidate_context.rs:3827–3833`, seed slot 2 | Release uses the **argument expression's** computation scope. `evaluate_release`, `protect_then_release` (237), and `untouched_scope` (265) describe removal of that scope, including inherited protection, while retaining independent scopes. | Slot 2 must be the actual outward route carrying those contributions, including occurrences inside the result effect. Seeding a release elsewhere is insufficient. |
| `candidate_context.rs:2970–2978`, `4460–4467`, replay | `compose_scopes(lower, upper)` calls `lower.then(upper)`. Zero IDs are identity shortcuts. Replay rejects a lower demand and retains the upper demand. `evaluate_then`, `compiled_execution` (287), and `ordered_associativity` (294) justify ordered evaluation once this route is authenticated. | Actual lower-to-upper contribution order and complete replay coverage, rather than a separately chosen sequence. |
| `candidate_context.rs:3280–3284`, observation | Evaluates a relation's transformer at empty inputs/protections, including identity ID zero. | This observer is a two-coordinate diagnostic; it does not validate arbitrary incoming states, full grants, or native handler behavior. |
| `candidate_source.rs:274–356`; `candidate_context.rs:2980–2984`, `4697–4713` | `owned` deduplicates a region forest; `fresh` allocates scope/input images and copies root origins. Context prepares accounting and accepts an externally supplied fresh `ScopedFlow`; enabled fresh transport rejects absent flow. | Neither clean file invokes `ScopeTransformer.remap` or shows the map closures supplied there. Shared map/state support is the first missing remapping premise at this boundary. |

The port laws discriminate order. `stamp_then_protect` (254) suppresses a **new** protection when the same input was stamped, retaining inherited protection. `protect_then_stamp` (260) retains an applicable earlier addition. A later release erases both additions and inherited protection for its scope; a later protection can add again if its guard remains applicable (`release_no_revival` requires a no-add premise). Therefore these operations cannot be reordered. Function argument contravariant `Swap` belongs to the separate context coordinate; it does not reverse the scope composition order. The retained port-recognition checks at `candidate_context.rs:3397–3430` compare against the same Rust constructors; they are useful producer checks, not an independent semantic oracle.

For `compose id g`, the design requires the argument's protection to be removed on the forwarded contribution also inside the output effect. The table identifies a candidate stamp/protect/release chain. It does not prove that every authentic forwarded contribution follows that chain or that an independent protected occurrence is represented by a distinct carried witness.

## Conditional caller injectivity derivation

The visible allocator supports a stronger premise than a transformer's private collision check, but only conditionally:

1. Before `fresh`, let scope cut `S` and input cut `T` be the respective inventory vector lengths. Assume valid inventory ownership: every live old scope/input ID is below its cut; each occurs in its owning region; `owned` is the deduplicated result of `owned(...)`; and no foreign IDs have entered the carried relation/state.
2. On successful `fresh`, each copied scope receives the current scope-vector length followed by a push; each copied input is analogous. Targets in each sort are therefore pairwise distinct and at or above its old cut. A hash map stores old-to-fresh associations; copying `scope_origins`/`input_origins` retains source attribution but is intentionally many-to-one and is **not** the injection argument.
3. If the actual caller uses this map on copied IDs and identity on other old IDs, then it is injective over the whole pre-copy allocated domain: two copied IDs have distinct targets, two untouched IDs remain distinct, and copied/untouched images lie on opposite sides of the cut.
4. If the same maps rename transformer and incoming state, and their combined support is contained in that old domain, every equality/membership comparison used by evaluation is preserved. The resulting finite injective partial maps can be extended to injective maps on Nat agreeing on that finite support; applying existing `evaluate_rename` to those extensions yields the desired content equivalence. This is a mathematical conditional application, not a newly checked Lean lemma or evidence that the authentic caller discharges the hypotheses.

The identity-fallback map need not be injective on the **post-copy** domain: old `a` mapped to fresh `b` and already fresh `b` left fixed collide. This does not establish a compiler bug; it explains why an authentic old-domain/support invariant and one shared map are necessary. Arbitrary post-copy state or reuse of the map at a later allocation stage cannot be included without another argument. Stateful closures also require stable images across transformer, demand, and carried-state renaming; the kernel's once-per-support-ID behavior alone does not ensure that.

The existing smallest scope witness at Lean line 431 already rules out the weaker premise: release scope 0, incoming protection 1, map both to 0. Local transformer support is a singleton, so its collision check passes; renamed evaluation removes 0 while evaluation followed by renaming retains 0. This packet cites that established abstract discriminator and does not rerun it, present it as a source-generated map, or duplicate the implementation lane's oracle.

**First missing evidence:** authenticate the external fresh-use remap invocation, its exact closures, and the old-domain support invariant for the transformer, demand and incoming state under one allocation instance. `fresh_transport_scoped` consumes supplied flow without reconstructing this proof. The dirty/quarantined scheme/receiver/effect/runtime owners were not inspected or modified. Even after that bridge, Rust loop refinement and complete source contribution/Call witness routing remain separate open premises.

## Checks, limits and parent application

Commands: read-only `cat`, `sed`, `nl`, bounded `rg`, `sha256sum`, `pwd`, `date`; all completed successfully. Initial four admitted input hashes matched. No Cargo/Rust/Lean/Lake/build/test execution, cache/environment/scratch/worktree, Git operation, mutation test, random seed or enumerated search was used. Oracle independence: this lane compares source construction and formal declarations; it neither authors nor reviews the implementation lane's BTreeSet oracle. Shared assumptions are the frozen Rust constructors and existing Lean content model; source correctness is not inferred from agreement between them.

Coverage is the named clean source producer, Function ports, replay composition, observation, inventory allocator and fresh-transport boundary. Omitted: external remap invocation, complete supported source forms, compilation, allocation failures/private-attempt disposal, Rust loop verification, complete carried witness and handler/native behavior. CPU/RAM were not measured; only short text reads/hash operations and the single leased note write occurred. Wall-time budget is 300 seconds; exact elapsed telemetry unavailable. No heavyweight process ran.

Original parent remains `YulangClosure.SourceProblem.InferenceSoundness`, with unchanged all-supported-source quantifiers and shared witness. Effect hygiene H, A/B, source/native identity, principality, termination and production are OPEN. The result documents the precise conditional use of existing laws; it does not discharge those parents. No main constructive proof or independent review was performed here.

Recommended next action / TODO `R144-FRESH-MAP-SUPPORT-1` (owner Luna): obtain an explicitly leased, frozen source-owner packet for the authentic fresh-use map construction and consumption. Require old allocation cuts, complete pre-remap support, shared map identity, and a falsifier where incoming support contains a new target. Keep quarantined paths quarantined until separately reconciled. The pending fresh compiler referee may review this handoff with the implementation candidate; no review is claimed here.

## Freeze and commit packet

Revision 1 is submitted frozen; writes STOPPED after this note and its read-only final hash. No descendants or other output paths. Artifact SHA-256 is supplied in the final handoff message to avoid a self-referential digest.

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-proof.md`.
- Baseline: `77cf25096f8271590b89380fc988d7e2dd11e7d6`.
- Dependency changes by this worker: none; initial dependency hashes recorded above. The implementation lane's concurrent test candidate needs its own final hash and review snapshot.
- Review status: UNREVIEWED research-only source/conditional derivation; no independent review or production/theorem closure.
- Checks already run: frozen-input SHA-256 equality; targeted text/declaration/caller inspection only. Compilation/execution/axiom audit NOT RUN by authorization.
- Proposed one-line research-checkpoint message: `research: map scope transformer laws to native caller premises`.
- Shared-record deltas intentionally left to Luna/curator: record this frozen receipt, preserve open source/native/H/A/B parent gates, and add `R144-FRESH-MAP-SUPPORT-1` only if adjudicated useful; no authority, manifest, index, task state or question bundle changed.
