# Formal permission projection r3: constructor read-back

Status: FROZEN, producer-authored source derivation, UNREVIEWED. Research and writes STOPPED on submission. Immediate successful read-back established under the validity conditions below; the constructor/capture/export endpoint-image obligation and parent, native, theorem and production gates remain OPEN.

## Objective, baseline and dependencies

Method: static source trace of the two admitted owners, applying the resulting equations only to frozen r2. No experiment or main constructive theorem proof. Primary-supplied baseline: `42e31a76658d744c7b7ecf39eae8bd1856450ee5`; not resolved with Git, which this packet forbids. Accepted semantics remain those recorded in r2: annotation policy §§1, 1.1, 1.2, 4 and withdrawn example §6; no semantic decision is reopened.

Observed SHA-256 values match the admitted contract:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| r2 contract | `34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877` |
| r2 source handoff | `f4a3ca3491d36e35e1d066aeafbe0e17f672e90014eeeb063b0cc6ca8a42b8d2` |
| r1 independent review | `a64d9bafde670a2c6e580741c8fc94e58b8d4b417c6e2768330ebf505f868203` |

Only these frozen predecessor documents and the two Rust owners supplied technical evidence. Required root/rule instructions were also read. Prior r1 review findings remain accepted: final Lean repair unchecked; graph export equations do not prove original-port provenance.

## Exact established equations and hypotheses

Let S be an ordinary reachable `InferenceSession` with its actual branch arena; execute a listed constructor successfully, yielding t. Read immediately in that same branch, before rollback, arena replacement or another mutation that retires t. Assume ordinary Rust/std semantics, successful allocations where the constructor requires them, and initialized-prefix/arena invariants established below. Then:

```
S.live_effect_term(p, r) = Ok(t)
  => S.store.term_view(t) = Ok(LiveVariable(Effect, p, r))

S.positive_function_term(a, ae, re, z) = Ok(t)
  => S.store.term_view(t) = Ok(PositiveFunction(a, ae, re, z))

S.negative_function_term(a, ae, re, z) = Ok(t)
  => S.store.term_view(t) = Ok(NegativeFunction(a, ae, re, z))

S.with_term_events(|arena| arena.positive_tuple(xs)) = Ok(t)
  => S.store.term_view(t) = Ok(PositiveTuple(ys)), ys = xs elementwise

S.with_term_events(|arena| arena.negative_tuple(xs)) = Ok(t)
  => S.store.term_view(t) = Ok(NegativeTuple(ys)), ys = xs elementwise
```

The tuple equality includes length, order, duplicate handles and each exact brand/index. These are source-qualified derivations, not machine-checked theorems or universal lifecycle claims. No tuple-named session wrapper occurs in admitted `lib.rs`; the final two equations describe the actual available generic wrapper and branch constructors, matching the constructor read-back premise described by frozen r2.

Live-term construction copies an ordinal; it does **not** validate that r is in `effect_bounds`, nor prove freshness, representative identity or row lifetime. Successful Function construction additionally establishes lookup-valid children of kinds `[Value, Effect, Effect, Value]` and signs `[Negative, Negative, Positive, Positive]` for PositiveFunction, with the opposite signs for NegativeFunction. Successful Tuple construction requires nonempty, lookup-valid Value children all of the tuple's sign. These child checks do not prove later lifetime or alias/representative facts.

## Derivation and source locations

1. **Wrappers.** `lib.rs:10542–10547` passes exactly `(Effect,p,r)` to `live_variable`. Function wrappers at `10566–10591` pass all four original arguments in their original positions. `with_term_events` at `10594–10619` invokes the constructor on `self.store.terms`, drains capacity snapshots and returns its result through error conversion. Sampling can return an error after the underlying term was allocated (`10607–10609`); therefore underlying constructor success alone is weaker than wrapper success. Successful wrapper return preserves the returned handle. Snapshot draining (`term.rs:955–958`) changes event bookkeeping. Resource sampling delegates through `lib.rs:10804–10818`, `10821–11009` to `sample_f4_resource_parts`; the term store is received immutably (`11017–11020`), mutable publication is accounting (`11426–11430`). No rollback is invoked in this wrapper. This is ordinary source-path evidence, not an audit of every test-only observer or external accounting helper.

2. **Exact node payload.** `term.rs:1205–1215` constructs `LiveVariable {kind,polarity,ordinal}` without substitution. `1230–1269` checks children before constructing exactly the four Function fields; checks are `1390–1402` and `matches_endpoint` at `1451–1480`. Tuple validation is `1272–1292`; `1295–1302` copies `elements` with `extend_from_slice` into an `Arc<[Term]>` and chooses the requested sign. There is no sorting or deduplication of tuple elements. `intern_structure` at `1358–1383` either returns an equal-node hit or interns the node and retains its backing.

3. **Interning invariant rather than freshness assumption.** `BranchTermArena::new` initializes an empty positions directory (`707–717`). Maintain `positions[n] = t => lookup(t) = n` by induction on reachable arena operations within a live epoch. `intern` (`1166–1202`) checks equality-key hits first; on a miss it reserves owners, calls `push(node.clone())`, then records that exact node/handle in positions and the active journal. Derived `Eq/Hash` on `TermNode` (`229–254`) compare full variants and payloads, including ordered tuple contents; equal hashes alone do not cause a hit. `Term` and `LiveVariableView` derive full equality (`110–113`, `131–135`). Thus a hit preserves payload equality without promising a fresh handle. This branch interner starts empty and does not search the immutable collected prefix for equal nodes; no cross-prefix uniqueness is claimed.

4. **Allocation/read-back.** `push` (`1083–1163`) uses a nonfull last page or reserves and registers a newly claimed page in `page_positions`, then returns the lineage brand plus page index. Page claim is aligned and checked: `TERM_PAGE_SLOTS = 256` (`24–25`), prefix alignment/sealing (`380–393`, `455–459`), shared checked atomic increment (`1405–1423`). `TermPage::push` (`1550–1555`) writes the node at the current initialized offset and advances the initialized prefix; `get` (`1567–1571`) reads precisely that initialized slot. `lookup` (`831–853`) checks brand, collected prefix, postfix floor, branch page directory and initialized offset. `ConstraintStore::term_view` (`lib.rs:3714–3715`) delegates to arena `term_view` (`term.rs:856–857`), which maps `TermNode::view`. The latter copies live fields (`275`) and Function fields (`279–299`) exactly and borrows the stored tuple slice (`305–306`). This composes into the equations above.

5. **Brand and branch validity.** `Term` has only brand/index (`110–113`), with no generation field. Collection brands come from checked atomic increment (`344–359`); immutable prefix identity is retained by sealing (`380–393`). Wrong brand returns `ArenaMismatch`. A sibling postfix term with the same lineage brand lacks a page-directory entry in this branch and returns `InvalidHandle`; matching brand alone is insufficient. Arena intern hits remain valid because new keys are journaled and removed on rollback (`803–821`). Commit (`789–800`) preserves nodes and the directory. These are representation facts, not proof that all actual permission terms survive arbitrary caller transactions.

## Lifecycle boundary: smallest structural stale-handle witness

Do not rely on the comment at `term.rs:590–594` as a proof that *all* rolled-back handles are never reused. It is correct for newly claimed page bases, but the existing last page is truncated and can reuse an offset. Source-derived symbolic trace, **not executed**:

```
start with an empty branch; allocate live(Effect, Negative, 0)
  // one retained page, initialized = 1
begin_route()
t = live(Effect, Negative, 1)   // fresh miss, same page offset 1
rollback_route()               // remove key, truncate initialized back to 1
u = live(Effect, Negative, 2)   // fresh miss, same page offset 1
t == u                        // same brand and index
term_view(t) = LiveVariable(Effect, Negative, 2)
```

All allocations are assumed successful. Three distinct live nodes and one rollback suffice from an empty branch: a retained nonfull page is necessary for this reuse route. `begin_route` saves its initialized length (`772–775`); rollback removes the added key but keeps/truncates the existing page (`808–817`); `truncate_to` resets initialized (`1558–1564`); the next push reuses that offset (`1550–1555`). Immediately after rollback and before u, t is `InvalidHandle`; after u it resolves to the replacement payload. Whole newly claimed pages instead lose their directory entry and future claims use monotonically new bases.

This refutes unrestricted persistence of opaque term identity across rollback. It is **not** a successful permission-projection counterexample: no actual constructor/capture/export path retaining this stale t was shown, and stale t violates the live-epoch hypothesis. Session rollback reaches this owner through `lib.rs:9646–9678`, `3523–3558`; caller disposal of every affected permission/domain handle is not established here. Invalid/stale lookup errors and this potential alias require that separate lifecycle proof.

## Applying the equations to frozen r2

R2 assumption A is now discharged for immediate successful constructors, and extends through additions/interning/commit that preserve the same live nodes. In r2's recorded source map, the live negative permission pair at `candidate_effect.rs:1544` therefore reads back as `(Effect, Positive, r)` and `(Effect, Negative, r)` for its same supplied r. The Function pair at `:1486` reads back exactly `(an,qan,qrp,rp)` and `(ap,qap,qrn,rn)`. Ordered tuple read-back supplies the Element-index step. These applications consume frozen r2 evidence; those source files were not reopened and no new equivalence of raw rows, canonical coordinates or annotation authority is inferred.

The **first remaining premise is r2 B**: the owner-matching permission record and parameter domain used at capture/export must still refer to this successful construction, with its term handles live in the same branch and no intervening rollback/replacement invalidating the association. Constructor equations alone do not establish it; the offset-reuse trace shows why mere later successful lookup cannot replace provenance/lifetime. R2 C (canonicalization/store association preservation) and D (successful capture/export) also remain explicit. Thus the endpoint-image result remains conditional on B–D; this packet supplies no unconditional constructor/capture correspondence, Lean bridge, native evidence or closure.

Recommended next action: primary obtain fresh non-author `compiler_referee` review of this frozen result and pinned owners, then admit an exact lifecycle/domain-preservation packet for r2 B if the review accepts these equations. No new source owner was opened to pursue B.

## Commands, coverage and resources

Checks: `sha256sum` on the two Rust owners and the three frozen predecessor inputs (all matched); bounded `rg -n`, `cat`, and `nl -ba ... | sed -n ...` source reads. Some early combined outputs were truncated; payload/view/page/wrapper/rollback passages used for the derivation were subsequently read in bounded outputs. No executable checks, tests, probes, Cargo, Lean/Lake, network, Git or descendants. No Oracle or independent reference implementation was run. No checker assumes transition rules; the equations are derived from inspected source under ordinary Rust/std assumptions. Seeds/ranges/mutations: none. The symbolic trace above is not runtime evidence.

Coverage is the two admitted owners and frozen r2/r1 review evidence. Omitted: actual end-to-end permission lifecycle, canonical representatives/aliases, complete rollback caller cleanup, external accounting/test-only observer implementations, source/native semantics and Lean checking. No claim of exhaustive absence of mismatches follows. One command process at a time except small independent read commands; no heavyweight build. Budget: 200 seconds, one CPU, 1 GiB RSS; CPU time, peak RSS and total elapsed time were not instrumented and are UNKNOWN. Observed model/effort metadata: UNKNOWN. Exactly one leased Markdown file written. No shared records or compiler files changed.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md`.
- Baseline SHA: `42e31a76658d744c7b7ecf39eae8bd1856450ee5` (primary-supplied).
- Dependency hashes changed: none observed; hashes above matched when checked; no final rehash after freeze.
- Review status: UNREVIEWED, producer-authored; frozen on submission; no independent review claimed.
- Checks already run: matching dependency SHA-256 checks and bounded static source inspection only.
- Proposed message: `research: derive formal permission constructor read-back laws`.
- Shared-record deltas left for primary/curator: record qualified r2-A source evidence and first remaining premise B; record existing-page rollback offset reuse as a lifecycle qualification, without asserting an actual permission bug; preserve r1 verification blocker and all parent/production gates OPEN; assign fresh review. No shared file edited.

STOP. No further writes or launched processes remain.
