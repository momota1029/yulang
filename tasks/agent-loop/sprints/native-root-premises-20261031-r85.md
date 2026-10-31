# R85 — establish or falsify native producer premises for the checked R84 Root

Status: ADMITTED bounded research sprint under the unchanged parent goal.

## Original goal and fixed scope

Parent: the original Simple-sub A/B soundness obligation at the existing R66 `Root`, with original quantifiers, accepted source domain and semantics unchanged. R84 now supplies a kernel-checked flattened finite-record Root construction for its stated `Primitive` premises; R85 asks whether the actual native source-drain / checked-emission producers establish the selection premises needed by that construction on the **same retained records**.

Decisive question: native `checked_internal_use_root` accepts a unique `(occurrence, typed pair)` root. R57/R84 additionally select Origins through state/relation-ID and route-based predicates. `RelationKey` interning includes pair, context, source set and scoped-flow identity; Origins are appended separately. Determine whether producer invariants entail R84 `originCandidates = [origin]` and unique R57 `originRead` on the same native inventory, or produce a source-reachable counterexample. A malformed arbitrary `Native` list is not a falsifier.

## Fixed outcome and success predicates

Return either (a) a source-derived constructor invariant and a Lean derivation that applies it to the R84 `Primitive` premises on the same indexed records, or (b) a producer-reachable source trace and formal countermodel showing native checked-root success while an R84/R57 selector premise fails. Preserve all competitors, occurrences, relation keys, origins and drain receipts.

Success must identify whether R84’s exact Root construction receives this premise, with a fresh independent source/proof review. A conditional lemma with an unproved producer premise is not success; it must name the exact missing source owner and falsifier. A counterexample is only source-qualified and does not by itself refute original A/B or authorize production.

## Baseline and pinned inputs

Branch `yulang3`, committed baseline `c4e594fc64d72dba30a73c64fcbf258eaebdfc32`. The Rust source files below are dirty relative to that commit but match the frozen byte hashes listed in the manifest and the existing FROZEN primary leases; use those exact current bytes read-only and do not stage or rewrite them. R84 candidate, accepted slot-4 stdin/result, outcome and review are pinned in the R85 input manifest.

Exact Rust owners: `candidate_context.rs` relation interning, root selection, source-drain receipt; `lib.rs` drain creation/completion and receipt retention; `candidate_receiver.rs` checked-emission extraction and consumed same-owner projection. Lean owners: R57 relation/origin selectors and R84 `originCandidates`, `Primitive`, `readRecords`. The manifest fixes byte hashes and source ranges. No additional source dependency without primary versioned admission.

## Lanes and exact outputs

**Read-only source lane** (`researcher`): only `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-source.md` is writable. Inspect the pinned Rust owner paths and return a producer-to-consumer field map, constructor invariants, duplicate/collision analysis and either the exact missing premise or source-reachable falsifier. No Rust changes, builds, tests, or Git.

**Constructive proof lane** (`lean_prover`): only `notes/theory/lean/YulangClosure/NativeRootPremisesR85.lean` and `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-proof.md` are writable. Build a source-aligned finite construction or adversarial producer-reachable model; state the actual connection to R84 `Records`/`Primitive`, and apply any proved result to the parent. Do not assume global uniqueness, omit Origins/relations, supply `Primitive` as a desired conclusion, or weaken claims. No Rust/compiler edits or Git.

**Independent reviewer:** primary assigns a fresh read-only reviewer to the frozen source map, proof, exact input and all theorem types/axioms. Review path: `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-review.md`. Neither author reviews their own contribution. Luna owns adjudication, records, all staging, commits and pushes.

## Resource envelope and execution gates

Total 4,800 seconds: source 1,000; proof 1,800; independent review 1,000; primary 1,000 including 500 closeout. Astra 0. At most two separately authorized Lean stdin invocations, each at most 120 seconds, total at most 240 seconds, existing `-j1 -M1024` and `LEAN_NUM_THREADS=1`. First call only after exact input and candidate review; one diagnostic-directed repair/call only if needed. Every call requires committed/pushed exact-input authorization. No fifth or fallback invocation.

No Cargo, Rust compiler, tests, Lake, project build, formatter, target, `.olean`, cache, scratch, environment, worktree, nested CLI or background service. Use only in-memory exact stdin and retain complete stdout/stderr in primary result artifacts. No performance activity.

## Non-goals, remaining gates and stop conditions

No compiler semantic changes, no source restriction, no production promotion, no claim that a finite/conditional bridge closes original A/B, no alteration of R84’s accepted Root candidate. Standalone R84 module/import closure, authenticated Rust extraction/execution, full native ancestry, original A/B, whole-language soundness/principality/termination and production remain separate OPEN gates.

Stop for source hash drift, unavailable/overlapping writer ownership, an ungrounded premise, counterexample, unsupported model/routing, any relaxed claim, checker/time/memory cap, exhausted invocation cap, user STOP or session end. Preserve 32 pending questions, 14 UNKNOWN worker rows and 12 QUARANTINED leases. Keep `current.json` at or below 16 KiB.

## Amendment 01 — original obligation and completed-receipt owner

Admit the original source-preservation statement §§1,3 and exact source-completeness discussion §§5–7 in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, plus all of `notes/design/2026-10-24-birth-level-scc-intrusion.md`, at the hashes and ranges in the updated input manifest. The proof/review lane may read these governing sources. This restores the original A/B context and the birth-level correction; it does not change either claim or close the parent.

Expand the pinned Rust read ranges to include `candidate_context.rs` completion indexing/receipt queries (2265–2335, 2990–3095) and `candidate_context_seed_with_formal` origin construction (3850–3895), and `lib.rs` drain receipt attachment (14272–14320). The observed question is whether the completed copy in `source_drain_completions` can satisfy a selector that reads `Origin.source_drain_receipt`, which was attached at drain start. Derive or falsify this from the exact producer path; do not infer mutability or completion synchronization.

## Amendment 02 — accepted R84 stdin recipe

Admit the hash-pinned R84 proof handoff `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-proof.md` as a proof/review read, per the updated R85 input manifest. Its §§ “Assembly and invocation gates” and its source inventory establish the accepted normalized prefix body and exact slot-4 recipe; do not reconstruct the prefix from an unpinned approximation. This grants read access only and does not authorize a Lean invocation.

## Amendment 03 — one diagnostic-directed theorem repair

Slot-1 execution was rejected with one reduction error at `pending_rejects_checkedRootGate` (flattened line 2271:20), recorded in the primary review receipt; `pending_rejects_checkedRootGate` and its dependent theorem currently carry `sorryAx`. Reopen the exact candidate and proof-handoff leases for one repair of that theorem's branch reduction only. Keep the lifecycle definitions, source model, quantifiers, conclusions, every competitor and the exact R84 parent unchanged. No source/compiler changes. Do not execute Lean. Freeze the repaired candidate, handoff, proposed stdin bytes/hash and diagnostic explanation. A fresh read-only reviewer must approve the exact second input before Luna separately commits/pushes its authorization. This is the sole second and final R85 invocation.
