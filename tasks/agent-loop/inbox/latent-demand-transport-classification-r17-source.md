# LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r17 — source handoff revision 1

Assignment-ID `LATENT-DEMAND-TRANSPORT-CLASSIFICATION/r17-source`; revision **1**. Sole author/worker `/root/latent_demand_transport_classification_r17_source`, session `LATENT-DEMAND-TRANSPORT-CLASSIFICATION-20261028/r17`. Requested **Sol/high**; observed model/effort **UNKNOWN**. No descendants/coauthors. Sole write lease: this handoff. Outcome **source-native-evidence, pre-run mapping only**. **WAITING / writes stopped** after freeze; resume only after Luna ACK plus frozen Cargo-1 logs, within the original 600s grant. Independent certification belongs to Luna's fresh reviewer.

## Inputs and original parent

Authenticated contract SHA-256 `19896d719176b6ffb84a4a1d51b03672246398c07539d4ffc8f80c14b879f53d` and manifest SHA-256 `5ff66c9237154d5d15161d68871c06b94d1de3e935edc838f4781f5758a3c121`. All **26 parent pins** authenticate. **445/446 file pins** authenticate at inspection: the sole mismatch is the candidate source actively and exclusively leased to the implementer, current SHA-256 `b08441c5f6609fcccac458f3e4d386855850af9a46312ffa6c30565589d93c99`. This is an observed delta, not a claim of candidate freeze/review acceptance. Stable mapping below uses frozen R16 source, SHA-256 `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`; inspected R17 loop switches only its silent wrapper to the observed core with unchanged inputs/evidence collection. Delta author and independent acceptance remain the implementer/reviewer's responsibility.

R16 source rev2 SHA-256 `95e95ca4ba5459d569fc1366cc059fea85ddd0f36524f5ecb68f39d40d1f6337` and outcome `1ec8efe2ce597501d632bc7c864b1646d1b4fd44718cf142ce3b679576551ed5` are reused only as finite prior-run evidence. R16 compiled and ran, `session.execute()==Ok`, four roots reconstructed, then empty `emission_cases` caused the unchanged panic. Its diagnostic call-only selection had two rows and no selected target; it did not locate a rejected guard.

Original parent `YulangClosure.SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean` (SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`):

```text
forall s x d a, p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e and p.sameScoped s x e a.
```

This proposition definition is not a proved concrete instance. No Lean checker or axiom audit is assigned or claimed. Preserve independent F1/FK1, arbitrary lawful source-client allocation, foreign-continuation and original scoped shared-witness quantifiers. All parent gates remain **OPEN**.

## Complete antecedent row inventory and identity map

Coordinates here are **R16 antecedents**, not predictions of R17 numeric IDs. All terms in the table have arena brand1 and trace invocation1. Join by full call/use/child/lower/upper/root tuple and actual same-run capture graph; equal-looking numeric nodes across graphs establish no equality.

| Row | Original source Call | Source captured relation/root; graph/node | Copied use/root/scope/input | Replay child/lower/upper; lower root; owner row |
| --- | --- | --- | --- | --- |
| 0 | call0, expression1, occurrence2, `f 1` in `invoke` | relation8/root264; graph3/node11 | use1/root299/scope32/input8 | 61/58/35; positive310; ValueRow44 |
| 1 | same call0 occurrence2 | relation8/root264; graph6/node11 | use3/root338/scope38/input9 | 119/116/93; positive349; ValueRow50 |
| 2 | call3, expression6, occurrence22, `h z` in nested `local` | relation150/root366; graph9/node12 | use5/root393/scope44/input10 | 191/188/168; positive402; ValueRow56 |
| 3 | same call3 occurrence22 | relation150/root366; graph11/node12 | use7/root430/scope50/input11 | 248/245/225; positive439; ValueRow61 |

The source specimen has independent `invoke id` uses and independent nested `local id` uses. Exact fresh-route owner/index must be read from R17 events; row0's R16 census explicitly joins Module route0/use1/occurrence12. The census filters Module uses1|2, so `source_use_identities=[]` for rows1–3 does **not** prove no source route. No later use occurrence ordinal is invented here. Expected owner families from construction are Module for copied `invoke` and Local for copied `local`; runtime owner/index is still pending. Native interfaces exist for call0 and call3 in all four R16 row diagnostics; demand roots are respectively264 and366. All lower/upper matches are true. Captures have `EvidenceCoverage { gaps:56 }`, source-bound ValueRow38/admission6 for call0 and ValueRow41/admission146 for call3.

## Constructors, imports and actual consumer

Locations below use frozen R16 `crates/yu-solver/src/`; R17 delta may shift only later test lines.

1. `shadow_apply.rs:4130–4168` builds Apply's negative Function demand with ordered argument, argument-effect, result-effect, result; retains original source registration in `NativeInterface`. `candidate_context.rs:3541–3583`, `candidate_context_seed`, local slot0 attaches `ScopedDemand { original_call, use_instance:0, root, output_scope, input }` from the exact occurrence. This source-call index is not a provider/permission certificate.
2. `candidate_scheme.rs:2761–2787` captures original bound/relation/root. `:2913–2948` publishes the same graph's retained negative Function index. `prepare_candidate_fresh_use`, `:4650–4758`, reconstructs root by that index, maps only local scope/input, changes use to the actual context use, imports bound snapshots and retains source-to-fresh relations. `begin_candidate_fresh_bound`, `:4760–4810`, admits the mapped bound with FreshUse cause and physical destination. Original capture, imported evidence, and physical append/readback are distinct evidence objects.
3. `candidate_context.rs:3054–3063`, `replay_demand_rows`, preserves each actual Replay dependency separately. It obtains demand from the child flow and checks actual lower/upper relation pairs against their ordered input bounds. No call-only uniqueness follows: two children share each original Call.
4. `authenticate_demand_transport_observed`, `candidate_scheme.rs:967–1129`, enumerates all Module routes followed by all Local routes. Matching requires both route use and retained context_use equal copied use. It then checks original root -> retained node/term; exactly one captured source relation with the same original Call/root and complete retained copied demand; exact snapshot import; zero demand transformers; mapped scope/input; negative Function and four ordered ports; unique FreshUse witness and physical admission/readback; retained Replay recipe; replay ancestry; same upper root; unique positive/negative Function nodes; typed port relation pairs; and unique accepted route. The test loop at baseline :8415–8426 is the actual emission evidence consumer.
5. `fresh_use_witness`, `candidate_context.rs:3065–3079`, independently requires unique Transport(parent=source, child=fresh, use_origin=copied use, reason=FreshUse) with exact child demand. `authenticate_replay_ancestry`, `:3085–3201`, requires exact source/fresh/copied pairs and ordered retained Replay, zero-step p1=h incidence, no demand on lower producer, preserved demand on upper/child, distinct typed FunctionPort children in Argument/ArgumentEffect/ResultEffect/Result order with Swap/Swap/Preserve/Preserve operations, actual stamp_input/protect_body transformer contents, and zero-step q=C consumer identity. p1, h, q and C must remain separately named; these supported zero-step checks prove no general rewritten consumer spine.

R16 per-row lower producer admissions are relation-keyed: lower58/admission56, lower116/admission113, lower188/admission184, lower245/admission240. Each has actual owner-emission/readback records in its row diagnostic, rather than evidence absent because call0 selection failed. Their existence alone does not authenticate demand transport or complete source Call.

## Stage interpretation and exact coverage limit

Each R17 event must be joined to the full row tuple, route owner/index and MatchingRoute. `original-root-absent` observes a rejection and continues to later routes. Other Rejected arms return `None` for the whole traversal. Thus one first rejection is decisive for that attempted row/route but gives no facts about later guards, and may prevent observing a later matching route. Accepted can also be followed by another matching route; the final Option and `multiple-matching-routes` matter. The caller skips rows lacking native call or copied ports before invoking the observer. No event is therefore not, by itself, proof of no matching route. Stage2 must classify missing prerequisites, absence of any matching event, or truncated traversal explicitly; unobserved extra routes remain a coverage premise rather than invented classifications. The fixed loop's allowed observer adds no route-census API, guard change or fallback. Any unclassified row or required extra route returns to Luna under the contract's incomplete stop condition.

Candidate first-stage rejection classes map to owning missing premises: root/source relation/capture/import/remap -> capture/FreshUse ownership; four ports -> reconstruct/term store; witness/admission/physical -> bound constructor and exact readback; recipe/ancestry -> replay and FunctionPort constructors; function-node/typed pair -> complete retained graph reconstruction. Classification records the first failed native evidence condition; it cannot establish that source semantics is false, or that all later checks pass.

## Application, TODOs and stop receipt

Source Generalize §§3.1,3.3,5.1–5.2 retains all simultaneous clauses, fixed provider/Established/OneShot dependencies, one original Shared binder, eligible Desc allocations at original scopes, per-frame ViewLogic before challenges and EventProof under actual events. Original Call includes callee computation, inert whole argument, actual returned provider/current receiver/receipt, entry, designated consumer and invocation return; body and invocation ports are not source-equal by fiat. Root retention and row freshness supply none of those universal local laws. The first-call source-fixed result applies only to its independently lawful old interpretation; its §5 leaves arbitrary eligible allocation open. The value-Generalize audit leaves full component/fixed/event consumer construction open. No new conditional theorem or source-qualified counterexample is claimed.

TODO `R17-TRACE-1` (Luna/Cargo owner): after independent pre-run ACCEPT, freeze the one exact attempt's four logs and byte hashes. Falsifier: build/load failure, changed inputs, missing row prerequisites, unclassified row/route, or first rejected native guard. After ACK+logs this same worker may use the remaining grant for rev2 mapping. TODO `R17-SOURCE-CALL-1` (Luna/source owner): derive the unchanged quantified Call/Generalize law from owning constructors/consumers or provide source-qualified counterexample, with full shared/provider/world/event telescope. R17 diagnostics do not authorize repair.

`InferenceSoundness`, source Call/shared-witness, Generalize allocation, complete source/native correspondence, effect hygiene, principality, termination and production remain **OPEN**. Approved Simple-sub generation/accumulation/propagation/levels/extrusion/qualifying intrusion/generalization are preserved.

Checks: read-only source/document inspection and SHA-256 only; zero tests/build/Cargo/Lean/Git/checker, source writes, descendants or background processes. Original grant600s, stage1 cap300s. Exact effective model/effort and leaf CPU/RSS/elapsed are UNKNOWN; no grant reset claimed. New/scratch paths: only this leased handoff. Revision1 frozen, **WAITING / writes stopped**, pending Luna ACK and frozen logs.
