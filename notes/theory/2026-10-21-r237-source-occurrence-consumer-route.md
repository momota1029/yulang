# R237 — Accepted source route to canonical-child consumption

Status: partial source/native audit; no route found in the bounded candidates; unreviewed. R71, R72, and the original Simple-sub claim remain OPEN.

## Question and scope

R237 searched for an accepted Yulang2 source/action history that joins (1) a third-owner physical effect-row slot, (2) an occurrence-qualified equality alias, (3) typed-drain consumption of the canonical child, and (4) a later production `Work::Bound` raw-key copy carrying that source lineage. The original quantifiers, accepted source domain, occurrence qualification, residual-lineage policy, and production boundary were unchanged.

The controlling contract is `tasks/agent-loop/sprints/simple-sub-source-occurrence-consumer-20261021-r237-rev2.md` (SHA-256 `3e4334c028067b62d1e5f1a31368efd8ce33f3e75de5314067bf2324bf4cca89`). R236's attach census and chronology artifact is `notes/theory/2026-10-21-r236-attach-lineage-induction.md` (SHA-256 `95dce8a15b7e9c57b94f6c5741cb7af1b4056fe32af66fb7adfe41db99c68144`).

## Candidate result

The R221-derived recursive callback source was accepted by ordinary candidate inference with no solver errors or candidate conflicts. Its loop Lambda was occurrence 9; slot 4 was relation 227 with pair `EffectRow(9) <= EffectRow(65)`. The complete trace contained 38,380 relation-consumer records. Its effect-row merges were `Effect(42) -> Effect(18)` and `Effect(43) -> Effect(41)`; the remaining observed merges were value-row merges. The production raw WorkBound lookups selected effect rows 28, 49, 54, and 52 (plus bottom/support entries). No selected raw item had the requested third-owner alias lineage, so the candidate produced no cross-owner alias hit and no canonical-child-to-WorkBound chain.

This is an exact accepted-source route miss, not a counterexample to the universal claim. In particular, the observed row merges do not join slot-4's source item to a later WorkBound-selected item. The consumer trace therefore cannot be used to infer the missing equality or consumer lineage.

A sibling-helper variant was also rejected during HIR lowering with `StructuralProjection`. That rejected source is not evidence about the accepted source domain and is not used to weaken or narrow the theorem.

## First missing edge

The first absent edge in the accepted candidate is before typed-drain selection: no occurrence-qualified alias connects loop slot-4's item lineage to a third-owner item selected by a production raw WorkBound lookup. R236 establishes that typed drains can consume a canonicalized child before dispatch reaches level-based extrusion, but this candidate does not supply the required source lineage into that child. R229's callback provider/formal owner bridge remains insufficient to create the missing slot-4 alias.

The bounded probe was removed because it yielded neither the requested alias-changing merge nor a target raw WorkBound copy. No production or source semantics changed.

## Evidence boundary and next obligation

The observations are from one accepted candidate and finite rejected variants. The probe and trace are test evidence, not proof of R71/R72 or the parent theorem. No independent review was performed. Full solver tests, semantic approval, and production remain open.

The next proof step must construct, from an accepted source and the actual attach/typed-drain operations, the occurrence-qualified lineage from a third-owner aliased item through canonical-child consumption to the later selected raw key and its independent consumer. The proof must distinguish key-context replay from relation-local post-check transport and retain rollback, retry, and residual premises.
