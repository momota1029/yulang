# Frozen implementation handoff — Replay constructor relation-admission repair r7

Sprint: `npair-replay-constructor-lineage-20261018-r7`, revision 7  
Contract SHA-256: `85d2eaefa427b238d554a69ec8049e238fd9ac446d6caded53e1eed1fb7e4d16`  
Assignment: r7 implementation repair, handoff revision 1  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN, closure 0.

## Authority, pins, and outcome

Only the existing new test function in `crates/yu-solver/src/candidate_scheme.rs` and this handoff were written. No context accessor, compiler behavior, source domain, semantic expectation, fixture, diagnostic, or natural inference was changed.

The implementation now selects a producer chain only when the complete relation-keyed admission set has length one. The final assertion checks that cardinality before the unique admission's complete `BoundKey` comparison. The typed emission/readback, relation identity, port, drain, fixture, authentication, and mutation-control observations and assertions remain in place. An extra same-relation admission with a conflicting bound can no longer be filtered out before uniqueness.

Verified frozen dependency pins:

- r7 contract: `85d2eaefa427b238d554a69ec8049e238fd9ac446d6caded53e1eed1fb7e4d16`.
- r6 scheme input: `d8c53522685e9bdfc1ba00380f222f4936d8d8df3302248fcde31e093668c484`.
- r6 context: `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`.
- r6 implementation handoff: `b4363b959ae7ab06696cc977da94819ce6c24e5642a5e0674bf9d538726c802e`.
- r6 conditional parent-application/proof note: `8d5cab69798da42c9de464f5dc8d568d647f3fa98e6d028289c8310e6b87d49c`.
- r6 test-removal scheme baseline: `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc` (reconstruction recorded in the frozen r6 implementation handoff).

After the edit, the r7 contract, context, r6 implementation handoff, and r6 proof note retain those hashes. Replacing only the r7 function edits in memory with their r6 text reconstructs the r6 scheme hash exactly: `d8c53522685e9bdfc1ba00380f222f4936d8d8df3302248fcde31e093668c484`.

## Source/proof boundary

The test observes the selected source Replay row, relation-keyed producer admissions, complete bound records, emission IDs/records and physical readbacks, then the existing propagation/authentication observation. This repair strengthens the instrumentation assertion ordering only. It does not establish runtime behavior, native correspondence, universal constructor coverage, complete `rho_u`, or the original parent theorem. Frozen r6 C1–C4 remain conditional; fixed-c supplier, complete `rho_u`, residual consumer, and the original parent remain open.

## Checks, budget, and stop

Checks performed: SHA-256 verification of all pinned files after editing; read-only in-memory reconstruction of the r6 scheme hash from the r7 source. No tests, build, runtime, or Cargo command was run, per contract. The 90-second implementation grant was not exceeded; exact active seconds and CPU/RAM are not independently metered. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. Astra: 0. No descendants or scratch files.

Next step in the frozen contract: fresh independent delta instrumentation review; only Luna may authorize the one exact test invocation after CLEAN. Worker writes stopped with this frozen handoff. Parent remains OPEN; no proof or production gate is closed.
