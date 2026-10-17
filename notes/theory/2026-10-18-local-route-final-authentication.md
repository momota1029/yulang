# Local callee route: source identity and final authentication

Status: constructive invariant and baseline source audit; candidate implementation correspondence pending frozen-source review.
Assignment: `NPAIR-LOCAL-ROUTE-FINAL-AUTHENTICATION-20261018`, revision 1.
Author: `/root/npair_local_route_authentication_proof`; descendants 0.
Requested model/effort: Sol/prover/high; observed model/effort: UNKNOWN/UNKNOWN.
Sprint: `npair-local-route-authentication-and-runtime-20261018`, rev1,
SHA-256 `3b54cd4c8350929015fa814abeefe441533daac398fa5437eb60244b272566a1`.
Baseline: `066cd49ec29a9718a884d44a325fe5580a382a66` (supplied by Luna; no Git operation).
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN, original conditions closed **0 -> 0**.

## Scope and parent application

This packet establishes the invariant needed to select a completed Local FreshUse for one actual source callee independently of later argument routing. It supplies a constructive implementation specification, and audits why the restored baseline and prior rejected candidate do not yet establish it end to end. It does not establish the original Operation fixed-c elimination, universal R/W/Z/domain action or active-consumer reflection. The original source domain, C1/C2, independent J1/J2, F1/FK1, Call, N-Transport, soundness, principality and termination retain their original quantifiers. No Local identity fact implies semantic contribution attribution or a foreign-continuation theorem.

The exact original parent and first semantic obstruction are retained in `2026-10-18-operation-original-formation-compatibility.md`, especially “Original obligation and frozen identity” and §1 step 5. This result applies only to the later `Install(g) -> Capture -> whole FreshUse -> g()/J2` routing component; it cannot manufacture the absent original paired interface or its licensed incidence. Parent closure remains zero even if this routing implementation passes tests.

## 1. Audited baseline and failed candidate

All contract-table pins, including duplicated rows, were independently rehashed and matched before reliance. The baseline has:

- `candidate_source::ConstraintBatch` local collection: allocate one global slot per binding in `source.bindings()`, store its `HirLocalId`, and schedule an `Action::Local` with that slot and the exact Name occurrence. Active initializers instead schedule `Action::Link`. Apply visitation pushes argument then callee onto the LIFO worklist, producing callee actions before argument actions before `Action::Candidate`.
- `candidate_scheme::route_candidate_local_run`: read `LocalScheme` at the slot, capture its actual graph, prepare a FreshUse, restore its actual bounds and constrain the fresh root into the source use's value. `commit_local_use` retains the graph, rows and remap maps. `RetainedFreshUseMaps::context_use` is the allocation identity to retain, not a value inferred from publication position.
- `candidate_call::observe(hir, store, state, index)`: authenticate the owning source Apply, original callee/argument, checking occurrence/cause and native Function ports. Its baseline signature has no GraphState and thus cannot authenticate a retained Local route.
- The actual final call site is `shadow_apply::CandidateInference::source_call`, which invokes `candidate_call::observe`; authentication solely in `InferenceSession::admit_candidate_fact` does not establish the final observer contract.
- `candidate_source::Action::LocalAnnotation` constructs an annotation interface and installs it through the same `LocalScheme` representation as ordinary installation. Thus `scheme.id == local` alone does not exclude annotated origins.

The rejected patch adds a keyed occurrence index and authenticates a Local tuple during `admit_candidate_fact`, but has no corresponding guard in `candidate_call::observe` or its final call site. It admits a callee Ascription by peeling and accepts annotated Local bindings through their common LocalScheme. The prior MAJOR is therefore a genuine missing end-to-end premise. Its index/accounting idea is reusable only after the complete correspondence below is checked.

## 2. Constructive state invariant

Let `O` be the immutable source owner of an actual Apply `A`. Resolve the callee from **A's actual callee edge**, not from an independently supplied Name. Peel Group and Block-final edges; record whether any Ascription edge was crossed. Resolve each expression from this same immutable source, with a finite traversal bound. Unsupported joins/Catch/result aliases retain their own refusal policy.

If the terminal expression `e` is a Local Name with local identity `l`, the eligible tuple is

```
T = (O, e.index, e.occurrence, l, s)
```

where `l.source_root() == O`, the owning binding exists in this same source, and global source slot `s` was allocated for that binding. Under the present restricted implementation envelope, eligibility also requires no crossed Ascription and no annotation on that exact owning binding. Same spelling, a binding in a different owner, and an annotation with merely a matching shape are insufficient.

Let `R` be the append-only vector of completed Local routes and `M` an occurrence-keyed index. Require:

1. For every key `o` in M, `M[o]=i < len(R)` and `R[i].occurrence=o`.
2. Each completed route has exactly one such index entry. Distinct source Name occurrences have distinct keys even when they resolve to the same binding.
3. For each route r, `r.local == source_locals[r.slot] == graph.locals[r.slot].id`, with a valid installed LocalScheme. Global slots are unique because collection appends one slot per immutable binding; they are not `HirLocalId::ordinal()` (which is owner-relative).
4. `r.use_instance` equals the very `fresh.context_use` moved into its retained maps, and the graph, rows, scope/context/evidence/bundle remaps all come from that same completed frame. Equality of two integers alone would not prove this provenance: the construction-and-move premise is essential.
5. A pending LocalUse has no index entry. Completed publication is a single synchronous transition after fallible bounds/link admission and reservation. No observer runs between index insertion and vector append.

### Preservation proof

Initially R and M are empty. Starting a LocalUse checks a valid slot, captures that scheme and prepares one FreshUse; it changes neither R nor M. Restoring another bound changes only the frame and live constraints, preserving the index invariant. On successful completion let `i=len(R)` and `o=frame.occurrence`. Reject a duplicate o, preflight vector/index storage and checked arithmetic, and reserve all work before the infallible publication step. Move the frame's retained tuple and maps into r, set `M[o]=i` and append r. Freshness of o preserves all prior entries; the new entry points exactly to the new route and the move proves clause 4. No route is copied, relabeled or chosen by vector position alone.

Now consider source callee occurrence `o_c` and a later argument Local occurrence `o_a`. They are distinct AST occurrences even for `f f`. Publishing `o_a` extends R at a fresh index and changes only `M[o_a]`; thus `M[o_c]` and its route remain unchanged. Induction covers any finite number of argument publications. Reading `R.last()` lacks this property and cannot authenticate the callee.

During a failed transaction whose saved completed-route length is k, remove each `M[R[i].occurrence]` for `k <= i < len(R)` **before truncating R**, then truncate and restore prior vector allocation if the journal owns it. Earlier entries remain valid with unchanged indices. Retained unused map capacity may survive failure; exact capacity restoration is not a correctness premise. Refresh accounted bytes from actual surviving capacities. Pending frame rollback restores the cursor or discards the private frame, and cannot publish a partial route. If rollback itself cannot continue safely, terminate the private inference attempt; no consistent published inference may expose it.

This is an inductive proof for these specified transitions. It does not assert that unfrozen candidate code already implements every transition.

## 3. Authentication at all three seams

A shared source-resolution helper should return either eligible tuple T, non-Local, or refusal. It must authenticate the actual Apply and owner before deriving T. Use it at source collection and again in final authentication, so a retained optional Local witness cannot bypass refusal by being absent or by naming an unrelated Local expression.

At source collection, retain T for a supported Local callee, including its global slot or a uniquely authenticated slot association. Reject annotated/ascribed Local routes in the scoped experiment before admitting the extension. Preserve ordinary non-scoped behavior and existing non-Local Ascription processing.

At `admit_candidate_fact`, rederive the same tuple from the owning source Apply, verify any retained witness exactly equals it, and check `M[T.occurrence]`, R bounds, route occurrence, local id, expected slot, source-slot local and installed-scheme id. Check the retained FreshUse identity with its own remaps. Absence of a completed route rejects an initializer-recursive Link; an endpoint relation cannot substitute for it. Ordinary candidate Apply demand generation/propagation continues through its existing negative Function ports.

At `candidate_call::observe`, perform this same source-derived verification with the actual solved GraphState, in addition to its existing native Function checks. The actual `CandidateInference::source_call` call must pass that GraphState to the checked helper (or execute the exact guard before the existing observer). Merely adding a helper without wiring this actual call is insufficient. If `observe` is callable elsewhere, require its own checked interface to enforce the invariant, or explicitly audit every entry point rather than assuming the public wrapper is the sole caller.

Soundness of this local authentication follows directly: successful checks yield an actual source callee T and one completed route r for exactly T's occurrence/binding/slot/use. Section 2 proves that later publications cannot change that selection. This is identity/provenance soundness of the retained Local route, not soundness of all graph freshening, semantic transport or inference.

### Annotation and non-Local parity

Refusal must depend on terminal Local classification. An Ascription wrapping a module or formal callee remains on its existing path. Peeling can record an Ascription flag and defer the new refusal until finding a Local terminal; a blanket `Ascription => Err` would broaden refusal and fail parity. Likewise, checking annotations across all bindings without restricting to exact owner/id either admits a foreign origin or refuses an unrelated binding. To admit an annotated Local in a future packet requires a complete same-owner annotation certificate through collection, installed interface, route and observer. This packet supplies no such certificate.

## 4. Finite work, accounting and unsupported cases

There are at most as many completed Local routes as scheduled Local Name occurrences. No rescan of R is needed for authentication. A hash index uses expected amortized constant-time lookup and linear retained storage; this is not a deterministic worst-case constant-time claim. Bounded source peeling and same-owner binding inspection cost O(E+B) per call in a simple implementation. Charge each traversal/binding probe, lookup/publication/rollback and rehash/move work in the scoped budget, or use a preaccounted bounded indexed association. No uncharged repeated full-route scan is justified.

Before fallible insertion reserve capacity and account its actual growth; retained map entry capacity contributes at least the repository's typed `(HirOccurrenceId, usize)` accounting amount, alongside route/frame/map allocations already retained. Scope work counters use checked arithmetic. Allocation failure and exhausted work refuse the private attempt. Reservation at frame start suffices only if no intervening nested Local publication can consume it; otherwise reserve at final publication. Geometric vector growth gives amortized linear move work; any journal restoration and index removal must be charged or bounded by the already reserved work. This proof does not certify allocator-internal HashMap overhead, wall-clock limits or a global theorem about the solver's existing accounting model.

`SCOPED_RECORD_LIMIT` additions and scoped work limits must be guarded by `scoped_experiment`; introducing a new unscoped call/local-route refusal changes ordinary inference behavior and is outside this result. Existing scoped-plan limits retain their existing scope.

| Case | Required consequence in this envelope |
| --- | --- |
| `f a`, both local, and `f f` | Distinct use occurrences; callee's indexed completed route survives later argument publication. |
| Group/Block final Local | Derive same terminal Local from original callee edge; authenticate binding, occurrence and slot. |
| Local Ascription or annotated owning binding | Scoped Local extension refused at source and final auth without complete annotation origin certificate. |
| Non-Local Ascription | Preserve existing observer/native behavior. |
| Recursive active initializer (`Action::Link`) | No completed Local FreshUse; cannot authenticate it as this route. |
| CatchBinder / If / Catch / unsupported result alias | Retain scoped refusal; no invented Local witness or graph-shape fallback. |
| Alias with no corresponding installed LocalScheme/route | Refuse rather than infer route identity from endpoint equality. An ordinary installed local initialized from an existing value is not rejected merely for being called an alias. |
| Failure after draft/reservation/bound work | No partial route observable; transaction rollback or safe private-attempt termination. |

## 5. Verification obligations and exact remaining owner

Implementation owner `/root/npair_exact_local_route` must return frozen source hashes and show actual final helper/call-site integration, source-derived optional-witness completeness, expected slot and fresh-use provenance, annotation refusal, non-Local parity, index publication/undo and accounted work. Independent compiler review owns acceptance; the proof producer does not certify the combined result. Required falsifiers include `f a`/`f f`, annotated Local, Ascription(Local), unchanged non-Local Ascription, unscoped cap noninterference, stale/missing/wrong occurrence or slot/use and failed publication. Actual runnable regressions are implementation evidence and do not prove universal semantic claims.

No compiler command, test, fixture, build, executable model or Git operation ran in this proof lane. Until the frozen implementation and fresh review establish §3 at actual source symbols, source/native correspondence for this extension remains OPEN. The useful result is the proved append/index preservation argument and the exact three-seam implementation criterion; original conditions genuinely closed remain zero.

## Frozen inputs and resource receipt

Baseline source SHA-256:

- `candidate_source.rs`: `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b`
- `candidate_call.rs`: `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359`
- `candidate_scheme.rs`: `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494`
- `shadow_apply.rs`: `d29d5f6488b5824eef5dc7902b70351b5bfae1ae3d7d014ec3629267443dbc83`
- `lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- Rejected patch: `a2e3f699ba53b79851fb34236cd96d8907cab516aa69b2c9c1abaa113350c2e1`
- Rejected-candidate closeout: `de4d3256346a8e8e6c7d4abd7d7ccb9ba8a1bdd6487dbdac41144696b6df8737`
- Original Operation formation: `30e6c9604f5d848ca4998295eced4acb158844944ca77982f2e82ff9b8341672`
- Original adoption decision: `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783`

Resources: <=300s cap; full300s conservatively charged at freeze, remaining0; CPU/RAM unmeasured. Static reads and SHA checks only. Exact leased outputs: this note and `tasks/agent-loop/inbox/20261018-local-route-final-authentication.md`; no scratch paths. Requested Sol/high, observed UNKNOWN/UNKNOWN. Writer stops after the frozen handoff. No descendants or unresolved descendant leases.
