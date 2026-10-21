# Sprint R238 — Backward source alias schedule from raw consumers

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Revision 2 supersedes rev1 only by pinning the exact fixed parent source; goal, quantifiers, source domain, method, leases, and resource cap are unchanged.
Baseline: `9f4bda630` (`research/simple-sub-intrusion`). R237 is frozen and pushed.
Authority: unchanged original computation-forwarding/Simple-sub theorem, R71/R72, approved Value-SCC occurrence qualification, approved contextual residual-lineage policy, R236 and R237 evidence.

## Fixed outcome

Advance unchanged R71/R72 by deriving the weakest source/native preconditions backwards from the exact later production `Work::Bound` and its independently required consumer. Determine whether an accepted source/action path can carry an occurrence-qualified third-owner alias from the canonical child to the exact raw-key lookup, or identify the first constructor/consumer premise that is not supplied. Preserve the original source domain, quantifiers, all physical siblings, selected residual lineage, rollback/retry and replay order. This packet may establish a conditional constructor fact or a smaller exact obstruction; it cannot close R71/R72 by finite search.

Use backward program slicing / weakest-precondition calculation over actual constructors, starting at `candidate_extrusion.rs::Work::Bound`, `candidate_effect.rs::candidate_transfer_bound_origins`, and `candidate_context.rs` replay/transport, then substitute through equality canonicalization, qualifying intrusion, source Actions and Value associations. Applicability requires source-derived transitions. A manually assembled graph is not reachability evidence.

## Parent and exact question

Parent gate: `R71-RAW-CANONICAL-FIBER-COVERAGE-1` with `R72-LATER-OCCURRENCE-1` and the original Simple-sub computation-forwarding claim. Current status remains OPEN. The fixed question is whether every independently required canonical-child obligation at a later copying occurrence is available with its exact lineage through that occurrence's actual raw-key lookup or another already-existing constructor transport. Do not assume the canonical bucket is saturated back to raw keys, replace relation IDs by endpoint equality, or identify replay's original `key.context` with later relation-local `post_check_context`.

## Success evidence and falsifier

A useful result must supply one of:

1. A constructor-derived weakest-precondition chain that can be translated into an accepted source/action history, including exact physical slot, raw/canonical keys, third-owner item alias, required fiber/RelationId, typed-drain order, consumer, discharge/residual states, and all same-class sibling slots.
2. A source-independent local theorem showing a stated consumer requirement cannot follow from the existing raw-key constructors, with the exact missing premise and no semantic change.
3. A smaller sufficient lemma applied directly to R71 that reduces its required lineage or schedule premise without changing its quantifiers.

Falsify a proposed chain that requires a rejected source constructor, unsupported provider/formal association, absent qualifying Value-SCC extrusion, wrong raw key, omitted same-class sibling, unrecorded transport witness, unlicensed consumer, collapsed residual lineage, or assumed equality between relation-local contexts. Finite source misses are not a universal refutation.

## Exact working method

- Invert the `Work::Bound` consumer first. It selects a retained physical slot, maps its visited bound to an operation-local `Key`, but preserves the physical `BoundKey` as raw `source`.
- The WorkBound arm looks up that exact raw source in `candidate_transfer_bound_origins`; it copies each raw-bucket relation with an Extrusion witness. Record how a canonical-child relation can enter that exact bucket, not just its canonical sibling bucket.
- A typed drain performs Transport, Context, then Dispatch. Record when a consumer reads an original replay `key.context`, when it samples relation-local `post_check_context`, and how per-RelationId discharge changes later state.
- Invert all four production `State::attach` routes from R236. Treat its no-witness helper as test-only. Follow equality canonicalization, parent-copy merge, extrusion, FreshUse restoration and ordinary owner emission separately.
- Substitute the approved Value-SCC occurrence condition and actual Yulang2 source Action/Local construction last. Do not infer a source route from row equality or a hypothetical graph.

The required consumer is the original theorem's consumer for the same independently selected residual lineage. If the available record does not determine that consumer identity, name the missing source/semantic owner; do not invent one.

## Lanes, leases, and limits

Serial primary proof/source lane, Luna only. No subagents, Astra, compiler edits, tests/builds, new syntax or sample execution. No safe implementation slice is established: inspected raw WorkBound and relation-local context owners implement distinct approved contracts, and R236/R237 expose no approved violation. If later evidence requires instrumentation, stop and issue a separate versioned lease first.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-backward-source-alias-20261021-r238-rev2.md`
- `notes/theory/2026-10-21-r238-backward-source-alias-schedule.md`
- `tasks/agent-loop/current.json`

Resource cap: 900 seconds total, serial work; no carryover. Freeze on a smaller decisive premise, an exact source-derived candidate chain, an authority/dependency/lease change, or budget boundary. No proof closure without fresh independent review. Commit/push only coherent contract/result/current-state paths after validating the whole outbound range.

## Frozen input pins

```text
9d93bf9e4579adf8ac88d05325431610757a1c844e85894b47308aa86a7a291e  notes/theory/2026-10-21-r237-source-occurrence-consumer-route.md
95dce8a15b7e9c57b94f6c5741cb7af1b4056fe32af66fb7adfe41db99c68144  notes/theory/2026-10-21-r236-attach-lineage-induction.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e  notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5  notes/theory/2026-10-19-r72-third-owner-prefix.md
08f178b448c711c43938ec26dd438c18bbee5d47ee4d11f1a03d2e88839f6597  notes/theory/2026-10-11-simple-sub-rebuilt-core-proof.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md (parent §§1,6–7)
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89  notes/design/2026-10-12-intrusion-value-type-association.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
```

The dispatcher proposal is non-authoritative until Luna issues this contract. No semantic, implementation, source-domain or review gate changes here.
