# Resumed bound restoration: conditional source correspondence

Date: 2026-10-11
Status: unreviewed research checkpoint; conditional derivation and operational obstruction, not suspension-contract closure.
Baseline: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`.
Producer: assigned `prover` leaf; no delegation, implementation changes, or independent certification.

## Objective and frozen statement

Authority is the private candidate suspension contract §4 (saved count, live indexed opposite lookup, current representatives, and mandatory deferral of unresolved cross-component incidence changes) and §6 (atomic route rollback and retained successful suspension). Contextual attachment/admission design §4 requires recorded replay order, complete parent derivations, extrusion/fresh-use transport, and actual parent/copy qualification. User approval of the suspension contract is recorded in that document. The prior retained-replay and owned-typed-drain notes are implementation handoffs, not premises proving suspension.

Fix one actual restoration operation `r`, its originally retained owner `o`, polarity `p`, bound `b`, accepted emission `e`, saved opposite count `N`, occurrence `O`, and cause `K`. These binders retain their original meaning throughout; neither canonicalization nor recomputation creates a replacement use/emission. Let `n` be its next physical opposite index, and let active replay `q`, when present, own its frozen ordered relation-ID batch and queued/consumed cursors. The original order means the operational order: indices `0..N`, direct-vector entries before exact-vector entries **at each lookup**, then lower-fiber cursor before upper-fiber cursor within the generated batch. It does not mean a frozen initial endpoint list.

The attempted conclusion is equality of the finite restoration-labelled event traces of (i) uninterrupted execution and (ii) execution interrupted at retained safe boundaries and resumed, on the same mutation schedule at corresponding operational boundaries. Events include physical emission identity, indexed opposite selection, exact lower/upper fiber parents and contextual replay construction, child transfer/completion, and occurrence/cause ownership. This conclusion does not assert termination for arbitrary contexts or equality of unrelated components' total event traces.

The following hypotheses are required, rather than inferred from endpoint equality:

1. Both executions start with the same full retained operation state, source-use/remap identities, physical bounds, relation/context records, bound fiber chains, evidence transforms, processing scopes, diagnostic state, worklists, and operation identity allocator. Suspension itself changes none of these restoration inputs.
2. The mutation schedule is aligned at the same child/lookup/dispatch stages. Mutations include physical direct/exact vector append, actual qualifying merges, fiber attachment/transport, context discharge, and dependency/diagnostic changes. The same callbacks receive the same state and perform the same ordered changes. An extra external mutation during the paused interval is not automatically part of the uninterrupted schedule.
3. The exact active replay batch and its lineage survive. Resuming an already generated batch does not resnapshot fiber heads, independently choose witnesses, rebuild its Cartesian products, or treat generated progress as completed consumption. Any required withdrawal/recomputation is performed in the same order before ordinary continuation in both executions; that lifecycle algorithm is a separate premise.
4. A suspended child retains its popped work, relation, Function stage, outstanding worklist, diagnostics/provenance and acknowledgements. Its parent advances only after complete typed drain and diagnostic completion. Every saved handoff identifies whether a child is unfinished or already acknowledged.
5. Every retained raw task is transported to current representative endpoints with its original relation as parent before semantic execution; its raw occurrence provenance is preserved. Every new opposite lookup canonicalizes `o`, `b` and the selected opposite using the current state. Equality transport retains contextual and attachment evidence, rather than substituting an unrelated fiber.
6. Suspension occurs only after the relevant frame/batch and accepted emission ownership are retained, and at an unambiguous transfer/completion handoff. The index is not advanced on `Suspended`. No failure commits a partial route; rollback restores the whole compared pre-route state, including operation cursors and identities. Both compared successful traces have valid vector indices and retained handles. Allocation success/failure and accounting policy are aligned.

Exclusions: universal source reachability, full diagnostic closure, certificate readiness/recognition, effect hygiene, complete Call, soundness/principality, general mixed-context termination, and F5 cutover. None is discharged here.

## Actual source bridge

All locators below refer to the pinned revision, not concurrent implementation files.

| Responsibility | Owning source | Established local fact |
| --- | --- | --- |
| Fresh-use inputs | `candidate_scheme.rs:1140–1179` | Captured bounds are restored in order; fresh transport, per-use context/bundle remaps and `FreshUse { antecedent, use_origin, source_bound, mapped_relation }` precede restoration. This maps an actual caller, not every reachable source. |
| Accepted physical emission | `candidate_extrusion.rs:406–564,655–675` | Admission precedes physical append; begin reserves restoration storage, inserts once, canonicalizes owner/bound, saves opposite count and retains emission/provenance. |
| Live physical enumeration | `candidate_extrusion.rs:567–627,677–721` | Count is direct plus exact on the current canonical owner. Each new index reads current direct length, then canonicalizes the selected endpoint. An active replay is driven before index advance. Drive itself has no bound-insertion call. |
| Saved ownership/cursors | `candidate_context.rs:43–86,1677–1713` | Operation stores `e,N,n,O,K` and active replay identity. Setting replay links it to its restoration. Advancing clears replay and increments exactly one index. |
| Fiber/product generation | `candidate_context.rs:2184–2215,2705–2786` | Fiber attachment creates a linked head with retained prior link. Begin replay snapshots heads; incoming use sets prior to `(None,None)`, so first quadrant enumerates full frozen lower/upper product in linked-list order and the second quadrant is empty. Children retain exact replay dependencies and both parent IDs; the task/batch and progress are stored. |
| Child consumption | `candidate_context.rs:1722–1775,2788–2820`; `lib.rs:11873–11905,12181–12231,12278–12295` | Transfer records queue ownership after reservations. Completion requires exact consumed index and occurs after drain/diagnostics succeed. The original `O,K` are passed to each restoration child. Baseline drains are synchronous and pop their frame on return. |
| Current relation endpoints | `candidate_context.rs:2505–2522` | Canonical task transport checks canonical endpoint agreement and creates a derived relation with retained parent/post-check context when endpoints changed. Raw task/relation remain available. |
| Actual merge/transport | `candidate_intrusion.rs:358–487,513–604`; `candidate_context.rs:2822–2839,2879–2891` | Only recorded parent/copy pairs in one actual dependency SCC are selected. Both sides are appended to parent before copy redirects. Origin transfer uses `ParentCopy` witness; equality canonicalization transports third-owner incidence too. Additional canonical fibers may be attached; incidence is not frozen. |
| Existing transaction undo | `candidate_context.rs:1497–1599,1600–1648`; `candidate_intrusion.rs:85–128` | Existing restoration and replay cursor undo is reversed, route-created IDs removed, evidence/fiber/progress records restored; forest and intrusion generation undo exists. This is not proof of complete future lifecycle/prior-frame rollback. |

These constructors establish the local data transitions. The pinned baseline explicitly has only complete/failure typed-drain outcomes (`lib.rs:12214–12218`); it does not establish hypotheses 3, 4 or 6 for an actual `Suspended` route.

## Conditional derivation

Induct on aligned operational steps, with a subsidiary induction on `n` and the active batch's consumed cursor. The induction invariant is equality of all retained restoration-relevant state, including lineage and provenance, rather than merely endpoint equality.

At begin, the actual constructor performs one emission and saves the same `N,e,O,K`. Resumption enters drive with `r`, so cannot reach begin's insertion again. If `n=N`, both retire and return `e`. If replay `q` is active, both read the same ordered child and acknowledgement index. Under the retained-child and completion hypotheses, they execute identical drain stages, mutations and diagnostics, then acknowledge exactly that child. Inserting a pause changes no transition. Completed children are not selected again by the consumed cursor; unfinished children retain ownership. Once the batch completes, both clear `q` and increment `n` exactly once.

Otherwise both compute the same current representative of `o,b`, use the same live direct length and index `n` to choose the same opposite, then orient the same lower/upper task. Both obtain the same exact bound fiber heads. For incoming-use restoration, nested cursor iteration creates the same ordered lower/upper dependency pairs and contexts, preserving shared parent IDs. The retained batch is installed before its children are driven. Any aligned callback append or merge updates both states before the later lookup, so the induction continues even when that later lookup observes a different endpoint than the original vectors would have supplied.

Therefore, under the frozen hypotheses, interruption is a stuttering step and the finite trace is identical, with one emission and the same product/child order. This is a **conditional derivation**, not an established theorem about the future suspension driver. It proves no commutation of differently timed mutations. It also does not prohibit the live algorithm from selecting the same canonical endpoint at two distinct indices: “no duplicate emission” concerns `e`, while completed-batch replay is controlled by cursors.

## Minimized operational noncommutation witness

Use distinct Effect rows `C,P,A,B,Z,L`, with a recorded actual parent/copy pair `(copy=C,parent=P)`. Choose an internal state in which that pair is not yet SCC-qualified:

```text
C.upper.direct = [A, B]      C.upper.exact = []
P.upper.direct = [Z]         P.upper.exact = []
P.lower.direct = [C]
```

There is a path `P→C`, but no path `C→P`. Restoration inserts positive bound `L` on `C`, saving `N=2`. Product index 0 selects `A`; after its child finishes, save `n=1`, with no active replay. For the witness assume its child does not create a path to `P`, and give the original restoration fiber and opposite fibers retained distinct provenance. This is a conditional internal state, not a constructed source program.

Now admit a negative direct bound `P` on `A` using the actual bound-insertion constructor. This gives `C→A→P→C`, so actual SCC qualification selects the recorded `C/P` pair. `merge_candidate_rows` transfers both sides, and its physical upper transfer appends `[A,B]` after existing `[Z]`:

```text
P.upper.direct = [Z, A, B]
rep(C) = P
saved restoration: N=2, n=1
```

At resume, current canonical owner is `P` and `candidate_opposite_bound(P,Positive,1)=A`. The restoration-labelled opposite trace is `[A,A]`; it retires at `n=2` without selecting `B`. If the external admission waits until uninterrupted restoration has finished, index 1 instead selects `B`, giving `[A,B]`, before that same admission/merge happens. Thus mutation-before-index and mutation-after-restoration do not commute. Canonicalizing the raw owner and task does not repair the changed indexed incidence.

The merge also replays canonical Cartesian combinations (`candidate_intrusion.rs:599–604`). That may propagate the relation involving `B` through another owner. It does not establish identical original restoration order/fiber/occurrence trace: ordinary merge replay uses `incoming_use=false` and the optional merge root, whereas this restoration owns its original incoming-use diagnostic provenance. No claim about an unrescued semantic failure follows from this trace witness.

If the **same mutation** is instead an ordinary callback at the same boundary before index 1 in both executions, uninterrupted execution also selects `A`. That is exactly the live behavior §4 preserves. Freezing `[A,B]` to “repair” resumed order would violate the specified algorithm.

This external mutation is **excluded while the incidence proof is unresolved**, by suspension contract §4's cross-component deferral requirement. It also fails §5's requirement that continuing independent components have dependency sets disjoint from the suspended continuation: it changes its owner representative, vectors and transported fibers. It is not a counterexample to a proven contract-permitted disjoint mutation. The baseline has no suspended scheduler establishing that deferral or its exact dependency inventory, and this note supplies no universal source-qualified reachability proof for the state.

## Exact remaining premise and deferral boundary

The needed source bridge is that a mutation admitted while `r` is suspended either occurs at its matched uninterrupted callback boundary or is deferred whenever it can change any remaining lookup or active retained obligation. This requires tracking owner/endpoint representative incidence, the current owner's direct/exact vectors **including the direct length separating lanes**, and the bound fiber/context/transform/provenance dependencies used by not-yet-generated replay; active batches additionally retain their exact relations, completion and diagnostic dependencies. A component label or unchanged saved count alone is insufficient.

Even without merge, appending a direct opposite before an exact one shifts the flattened index: direct `[A]`, exact `[X,Y]`, saved `N=3,n=1`; append direct `B` and subsequent indices select `B,X`, not `X,Y`. This is a second obstruction to incidence preservation, not a second equivalent proof attempt. Aligned same-component callbacks remain permitted and must retain this ordinary behavior.

One narrow completion handoff is also conditional. Nontransactional `acknowledge_replay` removes the completed replay immediately (`candidate_context.rs:1750–1757`), before restoration advances in its caller. A future pause there must retain an explicit completed stage or make parent advancement atomic; merely resuming the still-active absent replay handle fails. Transactional reclamation retains a completed replay still owned by a live restoration (`1605–1611`). The current synchronous baseline never exposes this interval as suspension.

This premise is correctness/obligation preservation (A), with a constructional dependency inventory at the mutation/scheduling owners; it is not grounds for restricting source inference. The saved emission, replay batch and original witnesses are already retained, so no inverse reconstruction layer is proposed. No two materially different derivations were retried against the same missing premise. Before another equivalent attempt, the primary should apply the required obligation-economy audit to the actual dependency retention/deferral owner. Classification does not close §4.

## Dependencies, checks and handoff

Direct dependency SHA256 values at the pinned baseline:

```text
83ebfc4b1fc917d842209a0d46e22188427a0b6523291073858bace0863055fb  crates/yu-solver/src/candidate_extrusion.rs
bc7e25c14e913d5f1c487723ead0fbbaf696bce80a1e6b756b7af4c04d6ebadc  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
7d3169a68d2413b58228f122c1e92a21d828e1a44e41743f4458eabb90ca580c  crates/yu-solver/src/candidate_scheme.rs
42bb81741d129cca8d9cf64a25f0a54c11fcf4cccc022f66c131c321752aa9de  crates/yu-solver/src/lib.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
```

Checks: static `git show <baseline>:<path>` with line-numbered reads and `git grep` for owning callers; SHA256 manifest computed from committed blobs; all seven compared HEAD blobs matched baseline at inspection. `git diff --no-index --check /dev/null notes/progress/2026-10-11-resumed-restoration-source-correspondence.md` produced no whitespace errors. No working implementation file was consumed. No Cargo, executable probes, tests, benchmarks or Git mutations were run. One reasoning leaf, sequential lightweight read processes, no child/build processes; reasoning stayed within the assigned 25-minute bound. Peak RAM was not measured.

Routing: requested role is `prover`; actual assignment identity is `/root/resume_restoration_proof`. The supplied callable schema supports `prover`, and the registered role omits model/effort pins with normal defaults `gpt-6.1-sol/high`. Parent launch arguments and effective runtime model/effort metadata are unavailable to this leaf: requested model/effort and observed runtime model/effort are unknown. No Astra job or reload is claimed.

Changed path: only this leased note. It is frozen for primary adjudication and independent review. No authoritative/shared record is changed. Next action: primary obtains a source audit of the actual suspended-mutation admission/deferral owner against the identified representative/vector/fiber dependency footprint, then tests the matching boundary without changing live callback semantics.

Commit packet: exact leased path `notes/progress/2026-10-11-resumed-restoration-source-correspondence.md`; baseline SHA above; changed dependency hashes: none in inspected committed HEAD (concurrent working edits excluded and must be independently revalidated by the primary). Review status: producer-only, unreviewed, conditional; no §4/6 closure. Checks already run: static source/caller reads, baseline/HEAD blob-hash comparison, and leased-note whitespace check. Proposed research-checkpoint message: `Record conditional resumed-restoration bridge and incidence deferral witness`. Shared-record deltas for primary/curator: record conditional aligned-schedule derivation, unresolved actual deferral/inventory bridge, and completion-handoff condition; preserve suspension/source/lifecycle proof gates as open.
