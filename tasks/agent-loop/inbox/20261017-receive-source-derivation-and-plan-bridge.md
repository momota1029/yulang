# Frozen handoff: two-Call source derivation and proposed plan bridge

Sprint: `receive-source-derivation-and-plan-bridge-20261017`, revision 1.  
Assignment: `receive-source-derivation-and-plan-bridge`, handoff revision 2 (revision 1 hash `977f92388d982e9d035a94fbb9063dc51a515ecd617149e30827a8a0885e027b`).  
Parent: user goal “continue until type inference and executor are implemented with proofs”; original parent and production gates remain OPEN.  
Baseline: `6dbb6ad2511b182c1761ecea73f25640eee68899`.  
Contract SHA-256: `bc5491798c230823a76fa77b777f998e6455811152aa6d978c3a4dd820066c3f`.

## Author, inputs, and output

- Role/worker/session: `/root`, Luna/high primary, current session. Requested `gpt-6-luna` / high; observed model and effort UNKNOWN.
- Exact outputs: `notes/theory/2026-10-17-receive-source-derivation-and-plan-bridge.md` and this handoff only.
- Proof artifact SHA-256: `597830364071d165c46f18175b51753521fb237b0bed67e08bec8781f24e251c`.
- Direct dependencies and hashes: frozen in sprint contract §§Frozen dependencies and in the proof artifact §7. Revalidate before independent review/integration.
- Work class: conditional source-constructor skeleton plus proposed bridge definition. Not a closed proof or source-qualified implementation.

## Parent application

For the original two-Call component, the frozen selected rules construct the formal/Name/Unit/Call source interfaces, the first-call receiving profile and the dependent ResultBind shape. At an actual Return, the two inputs remain tagged and use the original `mu_z` and `rho_c` maps. This identifies the source owner and runtime plan fields without asserting their actual source operands are all admitted.

The first exact unprovided source premise is an independently satisfying punctured caller context for `c_1`, at the same original `A_1,E_1,xi`, including the hypothetical `g:Value(A_1)` and its actual second-Call obligations. The native route also lacks its one anchored full MODEL. `c_2` separately needs the actual `b_g` result binding and its complete challenge. The complete source derivation `T` is therefore not constructed. No invalidity conclusion follows.

## Proposed bridge and falsifiers

The draft candidate `ExportPlan` consumes an original independently valid `T` and emits source-indexed EntryPlan/ExecPlan/ReturnPlan graph nodes. It preserves formal/annotation/substitution/source occurrence identity, the actual provider and entry, whole-carrier and complete-call slots, designated consumer, both tagged Return operands/maps, and future-entry instructions. Import validates all references against the same source graph and rejects missing/foreign/mismatched plans. Erasure and one-for-one source-event simulation are the obligations. The bridge cannot prove `T`, source admission, native MODEL, or caller/provider premises.

Falsifiers include a missing constructor action, mismatched source join, lost/retagged Return operand, different Return worlds, hypothetical future receiver minted early, omitted row converted to permission, foreign/missing plan accepted, or source erasure changing order/provider/guard.

## Review, repair, checks, coverage, and limits

Fresh independent compiler-referee review of revision 1 returned no blocking
or major finding and one minor finding: the original ReturnPlan bullet routed
every return packet to `b_g`, contradicting its separate `c_2` body-result
description. Luna accepted and repaired it. Revision 2 now routes `c_1` to
`b_g` and `c_2` to the original Lambda body-result destination. A bounded
delta review of these frozen bytes remains pending.

- Read and pinned the exact governing source/design clauses named in the contract.
- Checked current `execute → RuntimeProgram::from_hir` seam and actual RuntimeEvidence/Instruction owners by source inspection.
- No compiler-source edits, tests, builds, runtime execution, native probe or benchmark.
- Unknown historical reservations: 3 retained; no author child launch. Proof/coordination charge: 120s; initial review charge: 120s cap (exact wall time uninstrumented). Overall assignment budget remains bounded by 900s.
- Omitted: independently satisfying caller context, full native MODEL, every other source form, general source/native theorem, implementation and production.
- Worker state: artifact writing is complete; this revision is frozen for review. Descendant leases: none.

## Next step and mutual TODO

Delta review on revision 2: confirm that the corrected `c_1`/`c_2` destination distinction matches the original source Return/Bind owners and that it resolves the minor finding. No reviewer edits this artifact.

After review, Luna may draft the separately leased source-applicable importer contract, mapping the plan fields through `execute → from_hir → Lambda/Callee/entry/Return`. No compiler code lease is part of this sprint. Semantic adoption requires its own authority/review path. Preserve F5, Catch, NPAIR and parent theorem gates as independent OPEN items.
