# R71 raw/canonical fiber coverage: preserved slot fibers and the unsupplied converse

Date: 2026-10-19. Status: **UNREVIEWED SOURCE/NATIVE EVIDENCE; COVERAGE TARGET OPEN**.
Author: `/root/r71_raw_canonical_proof`, constructive leaf. No descendants or independent certification.
Sprint: `raw-canonical-fiber-coverage-20261019-r71`, revision 1.
Contract SHA-256: `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`.
Baseline supplied by Luna: `f375fd737`. Current live-byte pins checked directly; no Git operation by this leaf.
Exact outputs: this file and `tasks/agent-loop/inbox/20261019-r71-proof.md` only.

## 1. Parent application and actual result

The fixed R71 question is whether every physical bound selected by a production `Work::Bound` has its required executable fibers at the **exact raw key actually looked up**, or supplied there by an existing transport; alternatively a constructor-derived production-reachable failure can refute that coverage. The route is restricted to the two `lib.rs::dispatch_live_item` calls at 12572 and 12585 under `shadow-apply-candidate`. A direct helper call or an arbitrary native state does not establish that route's reachability.

The original type-inference/evaluator goal and accepted source domain are unchanged. Simple-sub A/B remain OPEN 0→0; R50 is NOT ADOPTED. No F1, FK1, foreign-continuation, source soundness, principal-type, generalization, evaluator or production claim follows. Top-level inference principles §§1–3 and §1.1(2) govern ordinary constraints, propagation, levels, extrusion, qualifying intrusion, generalization and actual occurrence-associated parent/copy retention. Concrete bound/fiber/evidence storage remains implementation evidence. No new semantic requirement is proposed here.

**Established source facts:** successful insertion certifies its actual canonicalized physical key; a successful canonicalization sweep forwards every captured attached fiber to its current canonical key and retains the original; `Work::Bound` copies every fiber on its exact retained raw key with an exact Extrusion transport witness. Third-owner aliases do not erase their raw slot or raw attached fibers. These are one-way facts; the square and case table below identify their composition precisely.

**Actual remaining premise:** after a selected raw item has become an alias, prove which canonical-key fibers must accompany that particular copying occurrence, and show their exact retained lineage is available through the actual raw lookup or an existing constructor transport. No reverse forwarding/saturation operation was found at these owners. The forward preservation result does not establish that premise. An argument using ancestral or payload equivalence must separately justify its correspondence with the required copying operation and retain each actual dependency/transform lineage; endpoint equality alone cannot provide it. This note does not replace R71 by a theorem that assumes coverage, and does not mark R70 ENTRY-WF true.

The result narrows R70's raw/canonical gap to an explicit direction and source transition: loss of an already-attached raw fiber through successful equality canonicalization is excluded by the inspected code; availability of every independently required canonical descendant at a stale raw source is not established. R70's local conditional transport lemma can now consume the first fact. Its operation target and R71 remain OPEN on the second, as well as R70's independent general ENTRY-WF and later drain boundaries.

## 2. Four separate maps and the commuting question

Let a physical slot be `s=(row, lane, index)`, including Value/Effect kind, selected polarity and direct-row/atom lane. Let `B(s)=(owner,p,item)` be its **actual stored** `BoundKey`, without canonicalizing its item. Let `C_t(k)` canonicalize both row endpoints at time t while preserving side. `canonical_value` and `canonical_effect` (`lib.rs:11576–11589`) change only row tags; Function terms and view/member IDs are not rewritten by row-representative lookup.

Let `F_t(k)` be the exact RelationId list reached from `context.bound_cursor(k)` using `bound_entry`. This is a key-indexed list, not a per-slot list and not the diagnostic `origins[k]` list. Duplicate physical slots may have the same key; `attach` deduplicates a relation at a key. Conversely one key may retain several RelationIds, contexts, source sets and scoped payloads. Evidence groups `(BoundKey, Option<RelationId>)`, physical emissions and FiberTransforms are distinct retained inventories.

For a selected deep-row Visit let m be its operation-local image of the canonical child key. The implementation constructs:

```text
physical selected slot s
    | read actual stored item
    v
raw source k = (visited canonical owner, p, stored item)
    |                                      \
    | exact bound_cursor(k)                 \ C_t on endpoints
    v                                        v
r in F_t(k)                             canonical key C_t(k)
    | actual Extrusion transport              ^
    v                                         | actual EqualityCanonicalization
copied key d=(fresh owner,p,m(C_t(item)))       | of each captured raw fiber
    |                                         |
    v                                         r
physical copied slot + emission/readback
```

The diagram is deliberately not an assertion that the two fiber branches are equal. `candidate_context_canonicalize_bounds` supplies `r -> c` at the canonical key, while `candidate_transfer_bound_origins` supplies `r -> e` at the copied key. It does not supply `c -> e` merely because c and r are related. Dependency and FiberTransform records retain different parents/from/to/reasons. Interning can return equal child RelationIds while still retaining distinct dependency/witness records; this is not permission to collapse them.

The missing edge is specifically any required canonical fiber `c in F_t(C_t(k))` back to the exact `F_t(k)` lookup or an independently justified copy construction that consumes its complete lineage. No key-equality or nonempty-origin argument supplies that edge.

## 3. Source-derived local facts

### 3.1 Insertion ties a real slot to a canonicalized admission

`candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:499–671`) canonicalizes owner/item before choosing one of the eight lanes. It calls `candidate_bound_origin_with_evidence(BoundKey(owner,p,item),...)`, reserves the emission, journals the physical owner, appends the item, reads the exact addressed slot through `candidate_physical_slot_bound`, compares the readback to that complete key, registers capture when requested, and emits the admission/physical/readback record. The readback check is actual storage correspondence, not a test assumption.

Thus, on successful return, the new slot's raw key equals the key admitted by that call **at the insertion time**. It need not equal its key after future representative changes. Admission occurs before append, so arbitrary partial/error states do not satisfy a converse “each admission has an emitted slot”; no such converse is used here. No every-slot-nonempty-fiber assertion follows either.

`candidate_bound_origin_with_evidence` (`candidate_effect.rs:522–583`) distinguishes modes and causes:

| Cause/mode | Executable relation attachment | Physical implication |
|---|---|---|
| OwnerEmission, either mode | `candidate_context_bound` creates/retains relation and attaches at bound key | Successful enclosing insertion emits actual slot |
| ExtrusionLink, scoped | `candidate_context_extrusion_link` with its own bound-purpose payload rule | Actual opposite-side link slot, not a copied selected-bound fiber |
| FreshUse, scoped, mapped relation supplied | `candidate_context_reuse_fresh_relation` validates retained FreshUse dependency and exact antecedent/source/use mapping | Physical restoration then emits the same canonicalized bound; validation does not invent missing relation |
| BoundTransport, scoped | relation is None | Physical bootstrap and metadata can succeed with an empty executable fiber list |
| BoundTransport, unscoped | calls ordinary `candidate_context_bound` | May add an Owner-style executable relation; it is not an exact replacement for source transport |

`candidate_context_bound_for:3678–3711` computes the canonical pair, retains the authentic processing/source parent, its post-check context, exact source set and permitted scoped payload, records Derived, then attaches at the supplied key. ExtrusionLink deliberately clears a deferred Value demand; ordinary selected-bound transport does not borrow that rule. Checked Allowance construction may use IDENTITY only through that owner's explicit `checked_boundary` logic. There is no new identity alternative in this note.

The copied bootstrap (`candidate_insert_copied_bound:416–430`) uses a snapshot with `MissingOriginAssociation` and BoundTransport in scoped mode. Its successful physical emission proves storage, not missing executable fibers. The following exact fiber loop is therefore essential.

### 3.2 The raw lookup copies every actually attached raw fiber

At `candidate_extrusion.rs:157–165`, a selected slot schedules both:

- child `Key(canonical_extrusion(stored_item),p,target)`;
- source `BoundKey(visited_endpoint,p,stored_item)`.

The visited endpoint was canonical when its Visit key was built. The stored item in the source is intentionally raw. The selected direct/atom lengths are snapshotted before the opposite-side source link; no typed consumer or merge runs in the immediate scheduling loop. R70's reviewed conditional worklist invariant supplies the local scheduling and valid-reference hypotheses only.

`Work::Bound:323–342` installs the mapped child physically, then calls `candidate_transfer_bound_origins(source,canonical_copied_key,Extrusion{initial,polarity,target})`. That helper (`candidate_effect.rs:677–718`) captures the **exact** `bound_cursor(source)`, saves next before each transport and iterates its full linked prefix. It does not look up `C_t(source)`, select an arbitrary relation on a matching pair, traverse reverse transport edges, or reconstruct an origin/fiber association.

For every observed parent r, `candidate_context_transport_witness_with_evidence:4091–4105` creates/interns a child with canonical destination pair, `post_check_context(r)`, exact retained source set and `transported_scoped(r,witness)`; records exact Transport dependency and FiberTransform; and attaches the child at the destination key. `transported_scoped:2744–2756` preserves the flow except the explicitly witnessed NegativeFunction demand-root remap. It does not identify distinct demands/providers/scopes.

On successful return the exact dependency/transform and destination attachment exist for every visited r. If the raw list is empty, the executable loop is legitimately empty. Origins are then separately admitted as metadata; scoped BoundTransport relation None cannot fill that list. Snapshot/transform coverage (`candidate_context.rs:688–818`) retains missing group/admission/emission/origin associations. A missing association is not repaired by a successful physical emission, nonempty origins or a transport dependency.

### 3.3 Canonicalization gives forward inclusion by transport, not set inclusion of IDs

After a representative write, `candidate_context_canonicalize_bounds:4005–4023` fixes `count=bound_keys.len()`, visits every captured `(from,parent,previous)` entry, computes `to=C_t(from)` and, if different, invokes EqualityCanonicalization transport. It then retains its extra Derived dependency at the canonical pair. `attach:3151–3167` only appends/deduplicates; this sweep does not delete or modify any old `bound_keys` entry/head or old physical vector item.

For each captured `(k,r)` with `C_t(k)!=k`, successful sweep therefore gives an attached canonical child c and an actual retained EqualityCanonicalization witness `k -> C_t(k)` from r to c; it preserves r on k. This is a relation between fibers, not literal `F(k) subset F(C_t(k))`: r may have a noncanonical pair while c has the canonical pair, and their identities/contexts can differ.

Representative lookup is stable within the sweep. Newly attached keys are already canonical for that forest, so the fixed captured count does not omit a second forwarding step required by the same representative write. This proves coverage of the captured raw entries by **forward** transports at that sweep, not all-path structural validity or a claim about attachments made after it.

Third-party owner o is included because the sweep ranges all `bound_keys`, not merely rows being merged. If o's physical item q has just become an alias of a, the old slot still stores q, old `F(o,p,q)` remains, and canonical children are attached at `(rep(o),p,a)`. There is no reverse loop attaching every canonical child at `(o,p,q)`.

### 3.4 Merge copies before changing representatives

`merge_candidate_rows:599–707` first canonicalizes copy/parent rows and returns if equal. For each side it reads each source physical item through `candidate_opposite_bound`; that helper canonicalizes both owner and returned item (`candidate_extrusion.rs:700–743`). The merge then builds its source key using that **canonicalized** item, installs the copied physical slot at the parent, and transfers its source fibers. Only after both sides does it write the copy's representative and invoke the global canonicalization sweep, then replay the retained parent's lowers.

For a stale source item q whose representative was already a before this merge, the actual merge lookup is `(copy,p,a)`, whereas the source slot may read `(copy,p,q)`. The preceding successful sweep for the earlier representative change gives the needed **forward** fibers at `(copy,p,a)`. This is the correct direction for this merge's lookup. It does not depend on reverse saturation. The current merge's own later sweep cannot retroactively justify its earlier reads; the induction must cite the previous completed canonicalization and absence of an intervening unaccounted change/partial history.

The physical source vectors remain intact, and selected source slots are copied as canonicalized items into the target. After the current forest write, old source keys forward to canonical owners. Equality does not rewrite third-party physical references in place.

## 4. Constructor induction boundary

The following is a preservation audit, not an assertion that every accepted history meets all R70 entry premises.

| Transition | Derived fact relevant to R71 | Unproved portion |
|---|---|---|
| Session initialization and graph start | `lib.rs:10143,10159,10178` initialize collected/parameter bound rows empty; `try_new_candidate:10223–10228` starts graph before later fact admission; `candidate_scheme:1162–1180` initializes context mode | Complete source scheduling, all references, scope inventory and arbitrary abnormal histories are outside this row |
| Ordinary bound generation | `apply_value_task:13935–13940` and `apply_effect_task:11820–11829` return to candidate owners when graph exists; candidate apply selects an oriented canonical owner/item and inserts via the physical/evidence constructor | This is not a global exhaustive audit of every possible mutation or recovery route |
| Signature-generated effect slots | `candidate_signature_effect:1861–2002` uses `candidate_insert_bound`, so its successful slot/evidence equality is covered | Source signature/view expressibility and all view validity remain their owners' premises |
| Fresh graph bound | `begin_candidate_fresh_bound:1855–1906` reconstructs owner/side/item; creates exact FreshUse transport when relation supplied; validates/reuses it at physical restoration | Captured graph completeness, source licensing and rollback/retry reachability are not established by this local reconstruction audit |
| One local extrusion | Retains selected raw key, resolves canonical child and emits/copies its exact raw fibers; representatives stable under R70's local invariant | Required canonical fibers beyond raw list remain the target, not an added hypothesis silently discharged |
| Representative merge | Previous forward sweep supplies earlier-alias source keys to merge's canonicalized read; later sweep covers all captured keys including third owners | Establish induction entry and every permitted interleaving/abnormal return before claiming all reachable histories |
| Replay/checked-bound registration | `candidate_context_execute_relation:3618–3649` can register another origin/fiber for an already physically registered Allowance; canonical owner and atom Allowance key retain the addressed slot key | Does not prove completeness of arbitrary canonical fiber growth on aliased direct-row slots |
| Context rollback | `State::rollback:2063–2089` removes newly discharged states/relations/dependencies/bound entries and restores prior heads | Full coupled physical-vector/forest/evidence rollback and later source resumption were not established here; no unconditional stale-key inference is licensed |

This table removes the suspected need for reverse transport **at the merge's canonicalized source-item read**, conditional on the earlier successful sweep. It does not remove the separate `Work::Bound` stale-raw lookup problem: that caller intentionally uses the raw item rather than `candidate_opposite_bound`'s canonicalized item.

## 5. Two attempted bridges and their exact obstruction

### Attempt A: representative-quotient equality

Propose `F(k)=F(C_t(k))` for every physical slot. Actual `attach` and canonicalization refute the derivation: they forward r to a child c and preserve r. Canonical buckets can accumulate from several raw keys. Their lists and exact witness parents need not agree. No physical ref rewrite or reverse saturation operation supplies equality. This is a failed proof method, not a source-reachable counterexample.

A smaller manual native pattern makes the gap explicit. Suppose a third owner o has one raw selected slot q with r attached at `(o,p,q)`, and a prior permitted merge has redirected q to a. Successful canonicalization attaches c at `(o,p,a)` with witness r→c. A later extrusion selects the old slot q, visits a and transports r. It does not thereby transport c as an exact parent. This pattern is only a **manual/conditional diagnostic**: this note does not derive the required source expression, qualification, merge, levels and later production caller schedule. It is not a falsifier, and does not prove that c is independently required by that occurrence.

### Attempt B: commute using ancestral or equal executable payloads

A more suitable candidate is to track each canonical fiber back to a fiber on some physical slot in the same representative class and copy that slot. Multiple physical slots are all scheduled, so a canonical bucket's accumulation alone cannot establish loss. For instance, if a real slot for a also exists, its raw `(o,p,a)` lookup copies c; a trace claiming omission without considering that slot is incomplete.

However ancestry is weaker than retaining the actual canonical fiber as a transport parent. The code records separate EqualityCanonicalization, ParentCopy and Extrusion witnesses, and evidence snapshots may carry different missing-association/physical-emission gaps. Replacing a canonical parent c by ancestor r requires a proved correspondence relation and cannot erase its witness lineage.

Even a payload-only commuting argument has an additional premise: `post_check_context` (`candidate_context.rs:3169–3174`) is relation-local, and `candidate_context_execute_relation:3649–3661` records discharges/residuals by RelationId. Equality transport samples the parent's post-check context at its own time; later raw-source extrusion samples r's post-check context again. The code does not derive equal discharge state for r and c from endpoint equality. A claim that both routes emit the same executable context must prove the relevant temporal discharge/residual relation, exact source/scoped payloads and dependency coverage. This observation is a proof obstacle; no source-reachable unequal-discharge witness is asserted.

Both methods leave the same coverage premise unsupplied. This packet therefore changes the proposed next method/input to a constructor-owned lineage trace and required-fiber consumer audit, rather than presenting a third renamed conditional theorem.

## 6. Exact next evidence and mutual TODOs

`R71-REQUIRED-FIBER-LINEAGE-1` — to Luna, retaining parent `R71-RAW-CANONICAL-FIBER-COVERAGE-1`. Owners: `Work::Bound`, `candidate_transfer_bound_origins`, `candidate_context_canonicalize_bounds`, `candidate_context_transport_witness_with_evidence`, and downstream `candidate_context_begin_replay` / scoped consumers. First missing evidence: characterize required fibers for an actual selected copying occurrence from the retained constructor/dependency/emission lineage, including whether a canonical child is an independently required parent or whether an actual lineage-preserving square using the retained raw ancestor suffices. Required inputs are the exact physical slot, raw key, canonical key, relation/dependency/transform identities and relevant discharge/residual states at both times. Required output is an occurrence-specific constructor/consumer proof, then its induction over the actual attachment owners. Falsifier: a production-qualified occurrence has a required lineage whose actual raw copy path has no corresponding retained transport; or a proposed square drops distinct witnesses, uses endpoint equality as association, or disagrees with relation-local residual/scoped behavior. New source law is not authorized.

`R71-REACHABLE-ALIAS-SCHEDULE-1` — to Luna/source owner. Use the manual three-owner roles o,q,a only as a target pattern. Derive, from accepted source constructors and exact `candidate_source` scheduling plus qualifying-intrusion records, a physical third-owner slot, a q→a merge, and later the actual nonrow Value root/receiver-level production call that visits that slot. Enumerate every same-class physical slot and its fibers before claiming absence. Preserve both scoped/unscoped modes and legitimate empty fibers. A direct helper invocation or graph whose transitions were assumed is not the required evidence. If reachability cannot be derived from the frozen inputs, record its first missing source/consumer symbol rather than infer a bug.

`R71-MERGE-FORWARD-INDUCTION-1` — to Luna. The successful earlier sweep establishes forward fibers for merge's canonicalized item lookup; finish the exact history/rollback preservation at `merge_candidate_rows`, `State::rollback`, owning physical row journals and the caller's retry/resumption boundary before using it as an all-path invariant. No global ENTRY-WF closure is requested from this small result.

`NO_SAFE_CODE_SLICE`: `candidate_insert_bound_with_evidence` and `candidate_context_transport_witness_with_evidence`/`candidate_context_begin_replay` were inspected; no established approved-clause violation is shown. If static source evidence remains insufficient, the minimal **proposed provisional instrumentation TODO**, under a separate Luna exact code lease, is an inert observer at the first selected `Work::Bound` slot and the preceding merge/canonicalization: record slot/readback, raw/canonical keys, full exact fiber/dependency/transform IDs and relation-local post-check states. Its exact falsifier is an accepted production route demanding a named lineage absent from the real raw transfer, after accounting for every same-class selected slot. An observer/test that merely assumes the alias state or desired demand does not satisfy that falsifier. This packet writes no observer, tests or production code and does not authorize a repair.

R70's general ENTRY-WF and later-drain/ack obligations remain separate. No additional external dependency, semantic decision or write lease was taken. A fresh independent reviewer belongs to Luna; this author cannot certify any combined proof/countertrace.

## 7. Reuse, checks, resources and writer boundary

R70's reviewed conditional result is reused only for its actual successful local worklist schedule, stable local representatives, visit-time selected prefixes, kind/polarity/level maps and exact raw-fiber transport. Its closeout explicitly keeps the raw/canonical gap, general ENTRY-WF and later drain open. Its mixed-polarity mutation trace rules out an immutable entry snapshot; its bounds/replay distinction is not restarted. Historical immutable graph or staged semantic proofs do not supply this live coverage premise. No historical failed/manual trace is promoted to source reachability.

Cross-lane falsification boundary, not a proof premise or new dependency: Luna relayed that `/root/r71_fiber_countertrace` independently considered the three-row third-owner alias pattern and found that the raw fiber survives merge and the exact copy lookup, with joint source/schedule reachability still OPEN. This agrees with the independently derived preservation case in §§3.3 and 5; it is not a missing-required-fiber witness or a production counterexample. The relayed frozen packet locator is `notes/progress/2026-10-19-r71-fiber-countertrace.md`, SHA-256 `28b237f0d9530bb539b08f6a75792e56bf4416ae51caaa22a986f03238ed3180`; its separate inbox SHA is `359bb42066abf2a24f4523928c7e321eb19f63da7c42a125ae6de47c94a8b16e`. These are Luna-supplied receipt metadata, not independently read/hash-checked inputs to this derivation. This author is ineligible to certify a combined result.

Checks: static reads/searches; R71 contract SHA-256 and 20 direct live-byte pins matched before writing; final byte/hash/whitespace receipts are in the handoff. Baseline match is taken from Luna's frozen activation receipt, not independently established with Git here. No tests, builds, probes, source execution, benchmarks, network/external contact, Git or nested CLI. No scratch/output outside the two exact leases; no descendants.

Requested model/effort: `gpt-6-sol` / high. Observed model/effort: UNKNOWN; request/configuration is not runtime evidence. Worker: `/root/r71_raw_canonical_proof`; session `current-conversation-2026-10-19-r70-extrusion`. Hard charged grant 900s from the 2400s sprint envelope; no carryover, expansion or time returned. Exact launch-to-stop elapsed, CPU and RSS are UNKNOWN; observed internal clock 2026-10-18 22:11:33 UTC, later 22:12:45 UTC. Static source checks have finite file/list bounds; no asymptotic or production runtime guarantee is inferred. Freeze/cessation is recorded in the one handoff after final read-only verification.

All new paths are the two exact leases above. This artifact is an unreviewed partial research result; R71 and the original parent remain OPEN. The next step belongs to Luna's intake/source-owner allocation, not a worker claimed to remain running after its stop condition.

## Direct dependency SHA-256 pins

All authors and prior status remain attributed in their frozen dependency documents. Author of the reused R70 theory: `/root/r70_ordinary_extrusion_proof`, with `/root/r70_extrusion_countertrace` contribution; R70 owner-map/closeout by `/root`. These authors are not independent reviewers of this R71 artifact.

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
6bb29d09fbf1440c964899815b95e06244cdd9ccc67ddf0dbe76d2016ec15b8e  notes/progress/2026-10-19-r70-extrusion-countertrace.md
4fbb70a13a205f4b0cef9990d7ad630c0bc956a611ebcdf4461a2886e1bd90e8  tasks/agent-loop/inbox/20261019-r70-research.md
c1b9a890d829edb77b065a09672b320c9fbe326e3d68c04a27d2fcf324dbd3a0  notes/progress/2026-10-19-r70-extrusion-owner-map.md
7987dd2e1018eec7d8bdbcadac8925e56007772f4709fc6dd98d8f5d6d7f1c1a  tasks/agent-loop/inbox/20261019-r70-implementation.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60  crates/yu-solver/src/term.rs
```
