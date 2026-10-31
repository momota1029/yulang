# Sprint EFFECT-PERMISSION-OCCURRENCE-FACTS/20261031-R65 — qualify fact readers by source occurrence

Status: ADMITTED_BOUNDED_RESEARCH. Primary: Luna (`/root`). Branch `yulang3`; baseline commit `a89bccbfb7b6123dff3522cc8cb000728f206fae` (= `origin/yulang3`). Revision 1.

Authority: unchanged `research/simple-sub-intrusion` goal and accepted Simple-sub semantics. R64 is CLOSED_INCOMPLETE; its structural results and the R55/R57 reader mismatch remain research evidence only. Preserve the original effect-hygiene parent, source domain, lawful histories, scopes and A/B quantifiers. Annotation permission remains local subtraction authority requiring matching inflow and selected handling. No global FactId-uniqueness premise, source restriction, semantic change or production promotion.

## Fixed outcome

Construct source-qualified readers in `OccurrenceQualifiedFactReadersR65.lean` matching the Rust selection order:

1. Enumerate every provenance edge at the selected `(HirOccurrenceId, slot)`.
2. Accept only exactly one edge at that key.
3. Resolve its semantic fact through the owning fact table.
4. Validate FactId, owner and endpoints before producing the source-fact record.

Build versioned reader bundles over the existing R45 Internal-incidence and R47 root-certificate inputs. Prove the qualified source-fact clauses, route-input agreement and same-use root agreement, including a successful finite witness where a distinct occurrence shares the same semantic FactId. Preserve R55 and R57 unchanged; do not claim equivalence with their global-FactId readers. R62 integration remains separate unless derived from these exact bundles.

## Success evidence and falsifiers

- Prove `readAt_iff`, dangling-fact rejection, same-key ambiguity rejection, foreign-key extension preservation and shared-FactId/distinct-occurrence success.
- Prove route-input and root-task agreement with the selected source coordinate, and construct the Internal incidence and R47 root certificates while preserving the same use, fact and raw permission entry.
- Retain all original premises and quantifiers. State explicitly that mathematical finite witnesses are not native runtime counterexamples.
- Rust adds a private borrowed occurrence/slot candidate view and lookup to the actual `InventoryPackage`, preserving every edge and validating the selected native fact. No inference, producer, routing or subtraction change.
- Fresh independent review attacks duplicate edges at one key, dangling/foreign facts, shared FactIds at separate keys, owner mixing, endpoint mismatch and exact theorem/axiom completeness.

Failure includes dropping any provenance edge, treating FactId as globally unique, resolving by a foreign owner, accepting a dangling reference, or claiming native multiplicity/runtime facts without source evidence. A source-qualified native counterexample would refute the relevant parent claim and never authorize production.

## Frozen inputs and lanes

R64 closeout HEAD: `a89bccbfb7b6123dff3522cc8cb000728f206fae`.

- R64 independent review: `bb5065a5f90e0e5106749b2ae8df90f42ee4fac4f4154f0438ba928f6d2b9bbd`.
- `candidate_receiver.rs` working baseline: `ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e` (uncommitted R64 type-error corrections; unreviewed and uncompiled; accepted into this exact R65 write lease).
- `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- R55 `SourceInternalContextR55.lean`: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`.
- R57 `ProviderNativeContextR57.lean`: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.
- R64 `BrandedInventoryOwnerR64.lean`: `790b1ac0a99f8a1582c442edfb352614e72cac28f13a9158c4e81a396474e86b`.
- R64 review, Rust and proof handoffs: `tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-{review,rust,proof}.md`.

**Rust implementation — `/root/r65_rust`, implementer Luna/high, 1,000 seconds.** Write only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-rust.md`. First authenticate the two R64 source corrections by exact reversal; then add only the borrowed occurrence/slot view and lookup. No builds, tests, Cargo, formatter, or other source writes.

**Constructive Lean — `/root/r65_proof`, lean_prover Sol/high, 2,600 seconds.** Write only `notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean` and `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-proof.md`. Use pinned Lean 4.35.0 stdin-only checking; retain full theorem types and complete transitive axiom reports. No Lake, cache, target, scratch or build writes.

**Independent review — `/root/r65_review`, compiler_referee Sol/low, 1,200 seconds (240 intake, 960 final).** Start only after both author lanes stop and exact snapshots freeze. Write only `tasks/agent-loop/inbox/effect-permission-occurrence-facts-r65-review.md`. No checker/build/test reruns, Git, cache, scratch, target or author contact.

**Luna primary: 1,200 seconds, including 500 closeout.** Aggregate sprint envelope 6,000 seconds; Astra 0. Existing checkout only. No worktree, environment, cache, target, scratch, build directory or new persistent generated output. Preserve all 32 pending items, UNKNOWN worker observations and quarantined paths.

## Parent application and OPEN limits

Success advances the source-fact clauses of the unchanged effect-hygiene obligation and supplies same-use typed inputs to R45/R47 under the fixed reader version. It does not close the original A/B, prove native runtime multiplicity, equate versioned readers with R55/R57, or close source-to-Native correspondence, outer successful Run, effects, soundness, principality, termination, full hygiene or production. R64 owner/token/TermView authenticity remains OPEN. Only Luna stages and integrates reviewed exact paths.
