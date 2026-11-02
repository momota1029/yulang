# R279 — Fixed-source public-route exclusion by HIR item census

Status: CANDIDATE until Luna's owner-view gate, staged GO receipts and exact leases.
Revision: 1. Original goal remains inference/effects soundness → R70 → R71 canonical-fiber coverage. Parent/A/B 0→0; Need_D, R70/R71 and full soundness OPEN. Original quantifiers, source domain and accepted semantics unchanged. NO_SAFE_CODE_SLICE remains.

## Outcome and proof edge

The unchanged 87-byte ASCII input is:

    my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }

The only source-qualified result sought is this successful-return census:

    for every normal Ok(hir) return of the specified production parse/HIR pipeline for this exact source,
    count { item in hir.items() | item is HirItem::Binding } != 2.

An at-most-one Binding census suffices, but do not assume it. Derive it from actual root-parser return/recovery behavior and actual HIR module lowering. Do not silently treat diagnostics or recovery as failure: account for every path that can return Ok(hir). A permitted source pipeline return with exactly two Binding entries is the direct falsifier COUNTERCASE_TO_CENSUS. A constructor/lowering error explains absence of that returned HIR only if all recovery-bearing Ok(hir) paths are also excluded.

Apply the reviewed R278 necessary guard: assemble filters hir.items() to Binding entries and requires exactly two plus no Expression before checking answer. Thus SOURCE_PIPELINE_ROUTE_EXCLUSION follows if the exact source pipeline cannot return a HIR with two Binding entries. This does not assert an observed assemble call or actual rejection unless actual argument production is separately established. A returned HIR with two Binding entries may proceed to later guards; it does not prove those guards pass.

This is a witness-local public-experiment result only. It neither rejects ordinary source nor establishes global unreachability, an accepted-source counterexample, compiler defect or soundness refutation. No actual answer=R or same-HIR root proof is required for count-based route exclusion; do not add it unless a distinct claim needs it.

Outcome classes:

1. SOURCE_PIPELINE_ROUTE_EXCLUSION: production owner equations justify the all-normal-return count-not-two invariant; R278 guard application is correct.
2. COUNTERCASE_TO_CENSUS: a permitted parse/lowering path for this source returns HIR with exactly two Binding entries, refuting the proposed invariant.
3. UNRESOLVED: owner coverage or a decisive source-to-census edge remains missing/ambiguous. Name the exact owner and do not infer from fixtures or expected results.

## R278 reviewed premise and immutable dependencies

R278 main contract: tasks/agent-loop/sprints/public-entry-guard-incompatibility-r278.md, SHA-256 26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233.
R278 frozen theory: notes/theory/2026-11-03-public-entry-guard-incompatibility-r278.md, SHA-256 bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e.
R278 frozen handoff: tasks/agent-loop/inbox/public-entry-guard-incompatibility-r278.md, SHA-256 fe761f634a1c4d17a516f93112c764eb40f284ad09dfd768034e7ba38e58a27c.
R278 independent review: tasks/agent-loop/history/20261103-r278-independent-review.md, SHA-256 7a67c5e08cd671e9588a07abe75e8e501185568dac0f64fb8a565bdbddbc6f5f.
R278 closed milestone: tasks/agent-loop/history/20261103-r278-closed-milestone.md, SHA-256 06eeb786cbc0a66d6f5645f528bd1b9d25ecbb0119b5f4ee8f332005950fe1c0. Its unissued 600-second stage is canceled; no R278 stage-2 lease transfers.

Source inventory: tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json, SHA-256 42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f (229 entries). Derive every source path from this inventory; no outside path is authorized.

Exact indexed R279 view:

- Ranges: tasks/agent-loop/sprints/source-hir-census-r279-ranges.json, SHA-256 3b484b3abe6c9d8c28f13985ebf2e0b1ddb4f978930483c53be279e354e1056d.
- View: tasks/agent-loop/sprints/source-hir-census-r279-source-view.txt, SHA-256 6817f43b2b4d44dbaf06fc6a582278054430d9e8d79974b223c49d2534c8c3b8.
- Binary-offset index: tasks/agent-loop/sprints/source-hir-census-r279-view-index.json, SHA-256 6cf12c5eed870bce75b665b797bc01e5ae2551c2e310681d8cd2d1f8590b1950.

The view has 27 exact payloads over 15 unique in-inventory source paths. R279-E001 is fixture bytes only. Production excerpts cover lexer/trivia/cursor/current-item classification, parse/header/root/binding/braced-statement owners, HIR public lowering, module root planning/lowering/item append, HirModule::items(), and only the local-source interface used by lowering. scan_trivia_part is included at crates/yu-syntax/src/lexical/lexer.rs with its full production definition and direct scanner helpers. No cfg(test) interval is admitted. The view is a candidate bounded read lease; stage-1 owner review may report an exact coverage gap before any census proof.

Prior R275-r3 authority for reusable owner ranges: contract SHA 4e30e9c048596a57da7cfa80fe1261e67e2db17f2ba8c07e70dc3961b02138c5, ranges 2cd3ad9dc9a66129a42ec11d8d45ef4b78a0a877d0d066dc262313d524c03c3e, view 6b3836953c876c40f2cda0b944ff5f8a8d912d179e5ac58f9e93c7e6d38e8373, index 0966c2429bb64896bd31de52f2e20609642c2a75bba6dae3cf5fec46ebcb94e5, corrected HIR coverage 61d22ccc8004305fb377a12556cd53550926c59cb5857a55b0f01f5921e775cb, entry index 74ec95494935e803296f8ab276b6237369253f73d3df57ec2bc5f33f12426481. Reuse only exact R279 payload intervals.

## Staged Sol work and resource accounting

Trial producer /root/sol_r274_source_acceptance, requested gpt-6-sol/high. Prior cumulative Sol charge 11,400 seconds. Total fresh R279 envelope 2,400 seconds:

| Stage | Seconds | Scope |
|---|---:|---|
| Sol stage 1 | 200 | Exact owner-coverage/integrity gate over this contract and pinned R279 view; no census conclusion and no output writes. |
| Sol stage 2 | 1,000 | Source-to-census implication, only after separate Luna GO following a passing/fully scoped stage 1. |
| Fresh independent referee | 900 | Source-first review of frozen census and guard application. |
| Luna | 300 | View preparation, stage gates, adjudication and record integration. |

Stage 1 first checks only this contract and tasks/agent-loop/history/20261103-r279-admission.md, then returns a fresh current-session WAITING acknowledgement. Luna separately revalidates top-level pins and inventory/view/index/range integrity, then issues immutable GO. After fresh resume acknowledgement, Sol may verify all 229 inventory entries, exact 27 view payloads, original interval equality and owner coverage; no census proof is authorized in stage 1. Sol returns READY or INCOMPLETE with the exact missing owner/bytes. Full 200 seconds charged on issue.

Only after stage-1 READY may Luna issue a separate immutable stage-2 GO under this unchanged contract. Stage 2 begins with a fresh resume acknowledgement and may prove/refute the census using only admitted ranges. If stage 1 identifies a needed owner outside the view, no body may be opened; Luna must pin a versioned view/contract extension before a separate GO. Stage-2 full 1,000 seconds charged on issue; cumulative Sol reservation after issue becomes 12,600 seconds. No reset/refund or stage-2 grant is currently issued.

Sol owns no files during stage 1. After stage-2 GO, exact output leases:

- notes/theory/2026-11-03-source-hir-census-r279.md
- tasks/agent-loop/inbox/source-hir-census-r279.md

No writes outside those two paths; no tests, builds, probes, Cargo, Lean, execution, fixture substitution, caller search, code edits, generated/scratch/cache outputs, descendants, external paths or semantic changes. Stop on pin mismatch, view/owner gap, COUNTERCASE_TO_CENSUS, proved exclusion or budget. Fresh reviewer is /root/r279_source_census_review, requested compiler_referee gpt-6.1-sol/medium, 900 seconds after freeze; not a producer/coauthor. Review receipt path tasks/agent-loop/history/20261103-r279-source-hir-census-review.md.

## Parent application and closure boundary

Even a reviewed SOURCE_PIPELINE_ROUTE_EXCLUSION only excludes the exact source from this public experiment. It does not close any unchanged parent premise. Parent/A/B remains 0→0; Need_D, R70/R71, accepted-source soundness, F1/FK1, foreign continuations and full production closure remain OPEN. No implementation path is admitted; NO_SAFE_CODE_SLICE remains.
