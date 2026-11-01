# R132 independent review receipt — handoff revision 1

Verdict: **FAIL pending correction of one blocking static source issue**.
Review was limited to the candidate and provenance gate; it is not compiler or
runtime evidence.

Reviewer: `/root/r132_route_provenance_review` (`compiler_referee`), read-only,
STOPPED. Frozen handoff revision 1 is 15,658 bytes, SHA-256
`509bdcc749b43033c588a33396c5d031a9ac6a8f023a27fbd0e50fa3979a46a1`.
All nine source pins match the committed baseline
`559021b7157b5f1fea949d08228aad13171d07b8`. The reviewer independently
reconstructed the candidate as 508,232 bytes, SHA-256
`3ccd2cd3de1107ca66a52ebcedfc5276c0311bc49edc71ff8a966fd9025ad143`.

## Findings

1. **BLOCKING — permission lifetime borrows the returned local incidence.**
   The adapter passes `&native.lambda` to
   `candidate_effect::State::bind_formal_entry_permission_use`. That binder's
   signature ties `occurrence` to the returned permission's `'a` lifetime.
   Returning `Some((native, permission))` then moves `native` while `permission`
   would borrow one of its fields. This is expected to fail static borrow
   checking (E0505/E0515); no compiler was run. A minimal candidate repair is
   to pass the authenticated session-owned `&origin.lambda` or
   `&recipe.occurrence` instead, then independently verify that the lifetime
   and identity remain correct.

2. **MINOR — direct current-representative equality can reject a valid stale
   capture after later row merging.** The candidate requires the graph row
   retained at capture to equal `intrusion.rep(raw_entry)` at adapter time.
   FreshUse canonicalizes captured keys again, so a later merge may change the
   current representative while preserving the route's captured row and
   mapped image. This appears to be a false negative, not a permission forgery.
   Revision 2 should compare current representatives of the selected captured
   graph row and the raw source row, or establish an equivalent capture-time
   relation that handles representative changes.

3. **MINOR — handoff records the wrong contract hash.** It lists
   `61b03747aa51f1659162b365b6a3d238c64fbe62df98d36f091ada09847f3e26`, which
   is the R131 contract. Actual R132 contract SHA-256 is
   `ba88ab578b9a851181eb603283fc80823eab7f4ed0b878df2103e1faa6a2519e`.
   Revision 2 must correct the receipt and be frozen under a sequential
   handoff revision/hash.

## Provenance review within scope

The reviewer found that the proposed adapter derives route, retained
incidence, arena, registration slice, and permission state from one session.
Source registration labels enter the context origin through the exact
constructor term and are retained structurally through capture/FreshUse.
Two Lambdas sharing a row or Function Term do not exchange registration labels
merely because of numeric equality. Duplicate/missing origins, recipes, or
permissions fail closed; source Lambda occurrence/index/parameter are checked.
Repeated route selection uses each route's retained map/context-use identity.
The existing positive Function, child-1, graph-row, native Function, mapped
Effect row, and permission guards remain. Capture and route transaction
rollback truncate context origins and published module routes.

Compilation, execution, Catch/provider consumption, Rust-to-Lean
correspondence, the original A/B claims, effect hygiene and production remain
OPEN. The reviewer ran no compiler, Cargo, tests, Lean, checker, storage or
environment probe; wrote no files and performed no Git operation.
