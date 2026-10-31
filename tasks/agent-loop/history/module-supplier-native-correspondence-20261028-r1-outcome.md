# Outcome — MODULE-SUPPLIER-NATIVE-CORRESPONDENCE/r1

**Disposition: CLOSED_INCOMPLETE.** The bounded source/native audit is complete, but its source handoff contains three evidence-attribution defects requiring correction in adjudication. The independently checked proof handoff and both OPEN supplier conclusions are accepted within the admitted scope. No compiler defect, semantic counterexample, theorem closure, or production authority follows.

## Frozen inputs and independent review

Sprint contract SHA-256: `13ef212b621918137054906ad8c7624b21d8fc855a57635368f5424ae2cc4a04`.

| Artifact | SHA-256 |
|---|---|
| Accepted r3 page-pack review | `2accece307d35ccc8dfb67fd171fa24a3a37d62a16d7cc6b56934e07acad998c` |
| Accepted r3 page-pack outcome | `679e182608764dbc1e4f4e5c9048062c5985fd204c3cb190c3594fe32b414a5f` |
| r3 manifest | `6c2c9fe80b294518b6ea8c8995e28a1b2604c3bb5e43f28e301c388219eb2c0a` |
| r3 generator | `e2990124a88099298abc5279a751c68ab87fefb2d066b5831bc59ff6bc249202` |
| r3 consumer | `4b50306376d8bafb187d400db7d683a6abdcb0aebfec6341c28e58804d63a6c7` |
| Source handoff (frozen, defects below) | `b7ef38b3e841372b34176f582e991a3daddbc3f6de519b230c63cdb59193037b` |
| Proof handoff | `707358daa9abab9830a3a2da71f1d47cce04d6c612802ea344bdecec83a2de0b` |
| Independent review | `a0bddc840260c099b84056ca88585cf1ccfba34c9ed0e2de076d9f5b11b773b2` |

The fresh nonauthor `compiler_referee` independently authenticated these pins and the adopted authority pins, then read all 18 admitted pages through the pinned consumer before reading the two semantic handoffs. No raw owner expansion occurred. Review measured at least 59.0159 seconds plus unknown startup/final reporting; full 200-second charge applies.

## Source-handoff adjudication

The frozen source handoff is preserved unchanged. Its first fieldwise conclusion must be read with these reviewer corrections:

1. **Major — unsupported target-index join.** Source handoff § inventory says the pending target “resolves through that index.” Page 006 shows construction of `definition_by_hir_id`; page 007 starts at `.get(&pending.target)`, omitting its receiver and assignment. Page 006 also omits the complete definition-record insertion establishing ordinal/table alignment. The pages do not establish `target = definition_by_hir_id[pending.target]`. Treat only the visible lookup suffix as observed; keep the receiver/assignment and registration alignment uncovered. This is an evidence gap, not a claim about unseen code.
2. **Major — dispatch and validation conflated.** Page 003 selects open-use from `active_uses` membership after indexed-use lookup. Page 012 later checks the parent and active roots. An indexed active use whose validation fails errors through open-use; it does not fall back to incoming. The exact branch split is: indexed active → open-use, with validation failure propagated; indexed inactive → incoming; absent index → no routing in this arm.
3. **Minor — wrong guard page.** Page 010 calls `validated_route_use`; page 009 contains the `cause.id == id` guard. Attribute the guard to 009 and its invocation/endpoint construction to 010.

No new page/source read is authorized by these corrections. The accepted package still supports the narrower observations in the proof handoff: ModuleDef target/occurrence and action identity (pages 001–005); component assignments and checks, subject to the missing join (006–008); cause guard and target-root → occurrence-value call direction (009–012); capture/freshening calls, receiving-owner selection, and successful `FreshRoute` retention (011, 013–015); actual `CandidateGraphExport` via `root_scheme_positions` (016); and a distinct observer `CandidateExport` channel (017–018). Unpackaged route, capture, freshening, activation, and export joins remain uncovered.

## Supplier and gate disposition

`ModuleNameSourceTypingAndAdmission` remains **OPEN**. No admitted field establishes the actual typed entry and source premise chain `E0`, prior `D_pub`, `Reg(C)`, actual `I_C`, lawful dependency-preserving `theta_C`, resulting `Gamma_C`, exact constructor-preserving lookup and branch-specific use/admission for the native occurrence.

`ModuleUseReceivingExportCorrespondence` remains **OPEN**. Even granting retained identities, the first unsupported semantic equation is `freshening lower = Phi_u(actual whole branch allocation root)`, preserving all dependent fields, original scope and shared witnesses. The actual graph export join and downstream routing realization remain open. Observer `receiving_export` does not prove actual `CandidateInference::export` correspondence.

The adopted fixed Published derivation may supply mathematical premises; lack of a runtime tag alone does not refute it. Neither successful routing nor structural identities are used to manufacture the missing typed premise. No quantifier or source-domain narrowing is accepted. Both suppliers, original A/B, complete Call/effects, callback → Call result → tuple `left`, N-Transport, F1/FK1, all parent/native/production gates, and `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remain OPEN.

## Resources and verification

Full sprint charge: source 350s + proof 300s + review 200s + primary 100s + contingency 50s = **1,000s**. Cumulative charge: **6,700 / 7,200s**; remaining: **500s**. Proof receipt reports at least 219.527453s plus unknown startup. Full 300-second charge applies. Source lane full 350-second grant applies. No refunds or reuse.

No tests, builds, Cargo, Lean/Lake, source edits, expected-output edits, or Git operations. The required static current-state check passed; it is not independent review or live execution. All gates remain open absent later direct reviewed evidence. Selector consultation is required at this sprint boundary.
