# LATENT-DEMAND-ROOT-VALIDATION/r16 — source handoff revision 2

Assignment-ID `LATENT-DEMAND-ROOT-VALIDATION/r16-source`; current handoff revision **2**, replacing revision 1 after Luna ACK. Worker/sole author `/root/latent_demand_root_validation_r16_source`, session `LATENT-DEMAND-ROOT-VALIDATION-20261028/r16`; requested **Sol/high**, observed model/effort **UNKNOWN**. No descendants/coauthors. Sole write lease: this file. Outcome class **source-native-evidence**. **STOPPED / writes stopped** after this final freeze. No certification or production authority claimed.

Luna acknowledged rev1 SHA-256 `90752b36c081de5a72071c357da9a346d618b691d4949ac221c6f7d13d4e308b`, then supplied the frozen Cargo-1 logs and authorized only the remaining stage2 trace mapping. Original rev1 content is retained verbatim below as historical context. Reauthenticated all **446 file and 16 parent pins** after Cargo: zero mismatches. Contract/manifest/candidate hashes remain exactly the rev1 pins. The accepted source domain and original theorem/quantifiers are unchanged.

## Observed result and same-run joins

The one contracted command compiled and ran the fixed fixture: **0 passed, 1 failed, 816 filtered out**, test time 0.11s. Cargo exit **101**, wall **116.375s**, CPU affinity **[0]**, peak sampled process-group RSS **1,859,252,224 bytes**, no limit termination. UTC start `2026-10-28T12:42:08.494526+00:00`, end `2026-10-28T12:44:04.869947+00:00`. Cargo `1.95.0 (f2d3ce0bd 2026-03-21)`, rustc `1.95.0 (59807616e 2026-04-14)`. These are authenticated primary-run receipts, not execution by this source worker.

All four observed root lookups succeed within trace invocation **1**. Coordinates below are joined within their individual graph, not across equal-looking roots (stdout line numbers):

| Graph | Capture / demand / lookup lines | Original call / relation / bound ordinal | Original root -> retained node | Context use | Negative Function children |
| --- | --- | --- | --- | --- | --- |
| 3 | 38 / 39 / 40 | 0 / 8 / 3 | Term 264 -> 11 | 1 | 12,13,14,15 |
| 6 | 41 / 42 / 43 | 0 / 8 / 3 | Term 264 -> 11 | 3 | 12,13,14,15 |
| 9 | 44 / 45 / 46 | 3 / 150 / 4 | Term 366 -> 12 | 5 | 13,14,15,16 |
| 11 | 47 / 48 / 49 | 3 / 150 / 4 | Term 366 -> 12 | 7 | 13,14,15,16 |

Every before-lookup event reports `formal_map_contains_root=true`, map length 1, and captured `EvidenceCoverage { gaps: 56 }`; every lookup returns the same capture's negative Function index. **The 56-gap observation persists.** Graph3/6 retain source-bound ValueRow38, root264, scope1/input0, admission/emission6. Graph9/11 retain ValueRow41, root366, scope15/input3, admission/emission146. Calls remain tied to the original source occurrence ordinals 2 and 22 respectively.

ReplayRows (stdout24) records four corresponding copied demands: call0/use1/root299/scope32/input8 with child61/lower58/upper35; call0/use3/root338/scope38/input9 with child119/lower116/upper93; call3/use5/root393/scope44/input10 with child191/lower188/upper168; call3/use7/root430/scope50/input11 with child248/lower245/upper225. Each row reports lower/upper matches true. R12 `consumer-result` (stdout50) and R11 consumer (stdout52) both record **`session.execute() = Ok`**. This establishes execution advanced beyond the former root-lookup ReceiptMismatch in this finite run, including actual reconstruction into later replay rows. It does not certify full demand transport.

## Exact next failure and observation limit

The panic is `candidate_scheme.rs:8428:14`, message **`the ordinary source fixture retains a FreshUse route`** (stdout34–35). The expression is `emission_cases.first().expect(...)`. The preceding loop at :8415–8426 applies silent `authenticate_demand_transport` to all four ReplayDemandRows and appends successful evidence; the vector is empty. Consequently none of those four calls returned accepted transport evidence in this run. Later raw-transformer mutation, four-port mutation and cross-route demand assertions after this point did not execute.

The separately instrumented diagnostic classifier did **not** identify the failed guard. Source :8310 chooses `target_row` only when `target_rows.len() == 1`; stdout24 contains **two** call0 rows (uses1 and3), so `target_row=None`. The `match (target_row,native)` at :8404 therefore skips `authenticate_demand_transport_observed`. `copied_demand=None`, `lower_producer=None`, `ReplayDrainStatus=NotRetainedReachabilityUnknown` and `unique_chain=None` in stdout30–32 follow this unselected diagnostic target. They are not proof that a copied root, producer or drain is absent for each actual replay row. No `ReplayAuthenticationClassification` line exists. The module diagnostic census also filters context uses1|2 at :8255; the second call0 demand has use3. This is a diagnostic selection limitation, without authority here to change test expectations or semantics.

Restoration/readback assertions before :8250 completed without panic, which is bounded evidence for the exact invocation/handle and physical slot assertions actually reached. The empty emission vector leaves full route/port/ancestry transport unresolved. Silent authentication can reject at numerous source :995–1126 guards; the existing log cannot distinguish source-relation/import/map/physical/replay/function-node/typed-port failures. Inferring one exact failing guard from the panic would overstate these bytes.

## Application to the original obligation and handoff

The reviewed same-graph index representation now has executed bounded support: four original roots reconstruct and the native session succeeds. The fixture exposes a later **demand transport evidence gap**, not another root-lookup failure. R16 remains a failed fixture and cannot be marked full successful validation; per contract Luna records CLOSED_INCOMPLETE. The original proposition and all missing source premises in rev1 remain open. In particular a successful session, matched scalar ports and retained evidence snapshots do not derive source-owned Call/world/provider/shared-witness preservation or arbitrary lawful Generalize allocation. `InferenceSoundness`, source Call/shared-witness, Generalize allocation, source/native, effect hygiene, parent, principality, termination and production remain **OPEN**, including independent F1/FK1 and foreign-continuation quantifiers.

TODO `R16-NATIVE-JOIN-1`: consumed the frozen one-attempt logs; root discriminant is positive, next concrete failure is empty authenticated emission evidence. TODO `R16-TRANSPORT-STAGE-1` (Luna/native evidence owner; requires a new admitted packet): obtain per-row observed authentication stages for each actual same-invocation replay demand and its matching Module/Local route/use, plus all graph node/term and imported snapshot joins needed by its **first** rejected guard. Use the current failed fixture/trace without merging sibling uses or selecting by call number alone. Falsifier: no unique source relation/import, wrong scope/input or ports, missing physical admission/readback, missing retained replay/function node/typed-port ancestry. The present packet authorizes no instrumentation edit, candidate repair or retry. TODO `R16-SOURCE-CALL-1`: unchanged original quantified source law; owned by Luna/source proof, with source-qualified counterexample or constructor-to-consumer derivation required.

Prior evidence reused within premises: R14 same-graph representation review; R15 pre-run closure failure only; original Generalize allocation and first-call fixed-instance audits, without upgrading them. New checks: SHA-256 reauthentication, read-only frozen stdout/stderr/argv/resources and owning source inspection. No Cargo/tests/build/metadata/Lean/Git/checker execution, source edits, scratch, descendants or background process by this worker. Stage2 uses the original 600s assignment grant; exact leaf elapsed/CPU/RSS and remaining time are unavailable (**UNKNOWN**), no budget reset claimed. All new/scratch paths: only this handoff. Writer **STOPPED**, all writes stopped; independent review and integration belong to Luna.

Authenticated log files under `isolated/latent-demand-root-validation-r16/logs/`:

| File | SHA-256 |
| --- | --- |
| r16-cargo-1.argv | f1fb430738c13ec6799b463b31dc8d13e7caf938e7d6e568bc51a4cb308773e9 |
| r16-cargo-1.resources.json | a32c0bf18f50749df61138b1ce4de358b2317dbd6e15a3b089de967c9ba8f9cd |
| r16-cargo-1.stderr | 550d76ea80653c335418053cff930fd17d129958f3d14e9d6fc66e2d218f73a6 |
| r16-cargo-1.stdout | 6e2125980e74d76f180f91a6086ff6ff0b4da0fb04fbd78dd26ed1e7e787b42c |

Primary-supplied bundle digest: `3db4390a1444cc21be994ff7bdc6ddfcc0f95a80a9e6c353771b72fe1a8d2a2c`; each individual file digest independently authenticated above. Bundle construction is primary-owned.

---

## Historical frozen revision 1 (verbatim; its WAITING status is superseded)

# LATENT-DEMAND-ROOT-VALIDATION/r16 — source handoff

Assignment-ID: `LATENT-DEMAND-ROOT-VALIDATION/r16-source`; handoff revision **1**. Worker `/root/latent_demand_root_validation_r16_source`; session `LATENT-DEMAND-ROOT-VALIDATION-20261028/r16`. Requested model/effort **Sol/high**; observed model/effort **UNKNOWN** (no effective runtime metadata supplied). Sole author: this worker; no descendants. Sole write lease: this file. Outcome class: **source-native-evidence, pre-run expectation only**. Writer **WAITING**, writes stopped after this freeze pending Luna acknowledgement and frozen Cargo-1 logs. No independent certification is claimed.

## Frozen inputs and original parent

Authenticated contract SHA-256 `d711f402f97681aa7e30a32b0e45e4f03c955297fef9b3216495d1140ce77d87` and manifest SHA-256 `8d399b67170dee03f72f451ffd49ba07e9cbb01649581ca5ac96bf0919fd06cd`. Independently authenticated all **446 file entries and 16 parent-artifact pins**, zero missing files or hash mismatches. The entries comprise 438 workspace inputs and 8 governing documents. This checks bytes, not independent compile-time closure acceptance. Candidate `isolated/latent-demand-root-validation-r16/crates/yu-solver/src/candidate_scheme.rs` remains SHA-256 `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.

R15 source handoff rev1 SHA-256 `b79c3ea16b426d4fe2ef07fe1022653c398b820323ba1f903f9e3b3ac4d7a2d8`; R15 outcome SHA-256 `3f6b80d5b60e5cc524ccf0bcbfde3d5bb9d07b72a0171f4732877f71d8c962d6`. R15 stopped at independent pre-run rejection for eight absent sibling cfg(test) literal inputs; **no R15 execution occurred**. Its expected joins remain a source map, not observed runtime facts. R16 adds 20 byte-pinned compile-time inputs while preserving the candidate.

Original parent `YulangClosure.SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean` (SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`), has type:

```text
forall s x d a, p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e and p.sameScoped s x e a.
```

This is a proposition definition. `CoreComposition.native_success_elaborates` independently assumes NativeCorrespondence, InferenceSoundness and Elaboration; none is discharged by the composition. Declaration reading here is not a Lean checker audit; no Lean execution or axiom audit is claimed.

## Source obligation and native trace joins

Governing source Generalize selection: `notes/design/2026-10-08-source-generalize-definition.md` SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`, selecting `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1,3.3,5.1–5.2, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`. Original Call requires original callee computation, inert whole argument, actual returned callee, current receiver/receipt, actual entry, designated consumer and invocation return. Body and invocation ports are not source-equal by fiat. Generalize retains the whole simultaneous component relation; fixed provider/Established/OneShot dependencies and one original Shared binder stay fixed. Each independent incoming frame allocates only eligible Desc declarations at original scopes, ViewLogic before its challenges and EventProof under actual events; aliases share their frame. Native index retention is not this allocation judgment.

Read actual R16 snapshot producers/consumers; locations below are in its `crates/yu-solver/src/`:

1. `shadow_apply.rs:4130–4168` constructs the four-port negative Function demand for Apply and retains its original source-call registration. `candidate_context_seed`, `candidate_context.rs:3541–3583`, local slot 0, constructs `ScopedDemand { original_call, use_instance: 0, root: introduction.demand, output_scope, input }`. The actual whole-Value rewrite at `:3659–3663` may change root only to the copied upper negative Function. This is native provenance, not an event/permission grant or complete source Call law.
2. `capture_candidate_graph_inner`, `candidate_scheme.rs:2761–2787`, interns each captured bound relation's demand root. Candidate publication `:2913–2948` retains that same capture's endpoint index in `negative_formal_roots`, checks a negative Function and conflicting index, and preserves prior formal entries. The reviewed equation remains `M'_g = I_g restricted to (F_g union D_g)`. No formal-domain or FormalPermission is created. The latent-demand insertion has no separate publication trace event; absence of a formal-publication log for that latent root is not itself failure. Join its capture event to the later lookup in the same graph.
3. `prepare_candidate_fresh_use`, `:4349` onward, allocates a context use and reconstructs graph terms. At `:4650–4696`, correlate `latent-demand-capture`, `fresh-use-demand-before-root-lookup`, and `fresh-use-root-lookup` by **same test/session invocation, graph_id, original call, relation, original root, node index, bound ordinal and negative polarity**. Graph-local nodes/terms cannot be joined across graphs by printed shape. Positive root discriminant: `formal_map_contains_root=true`, `owner_returned_index=Some(i)`, graph node `i` is a negative Function, and execution advances past `terms[i]` reconstruction. A lookup line alone does not expose the latter check's success. R13's historical coordinates were invocation 1 / graph 3 / Term 264 / node 11 / bound ordinal 3 / relation 8 / call 0 / use 0; they must not be assumed to recur numerically in R16.
4. Scope and input are mapped using this FreshUse's owned region remap; `use_instance` changes to `context_use` only when the input is local. Evidence import occurs after lookup (`:4701` onward); then `begin_candidate_fresh_bound`, `:4760–4810`, creates the mapped relation/physical admission. For later success, join the original relation and imported source-bound snapshot to this use's fresh relation, demand, output scope/input and exact physical destination. Original `use_instance=0` and the new context use have distinct positions in this chain.
5. `authenticate_demand_transport_observed`, `:967–1130`, independently checks Module/Local route/use, original root and unique captured relation, copied demand, imported snapshot, scope/input maps, negative Function with four ordered typed ports, FreshUse witness/admission, physical fiber/readback, retained Replay recipe, ordered replay ancestry, typed port relations and unique route. Capture membership proves none of these later conditions. The fixed fixture `:8158` first requires `session.execute()` success, then authenticates restoration invocation/handle/relation/readback and rejects cross-route/substituted evidence. A panic before those assertions does not validate them.

Keep antecedent `EvidenceCoverage { gaps: 56 }` as the prior finite-run observation until exact R16 output changes it. A retained snapshot is not an eligibility certificate. Missing load/build/execution means no R16 native guard result; failed fixture means freeze the first actual failure, without retry or new inference from absent later stages.

## Parent application and remaining premise

R14 review ACCEPT only supports same-graph representation retention. The universal source premise still missing is: every retained nondefault ScopedDemand and every lawful source-client allocation reconstruct the **same source-owned Call demand** under its translated original telescope, preserving provider/shared witness, fixed executed/event dependencies, source permission, all four ordered ports and all source clauses. Owners: source Generalize §§3.3,5.1–5.2 and original Call rules; native `candidate_context_seed`, capture, `prepare_candidate_fresh_use`, `ScopeInventory::fresh`, FreshUse/Replay authentication.

The first-call source-fixed result (`notes/theory/2026-10-16-first-call-fresh-use-semantic-application.md`, SHA-256 `9d5ec6a410c2b358187c1fcf105ba9efe5b2f5f9f4ede37ea2bb5364801ff46b`) reuses an independently lawful old interpretation; its §5 explicitly leaves arbitrary eligible Desc/telescope allocation open. The value-Generalize source emission audit (`notes/theory/2026-10-11-value-generalize-source-emission-law-proof.md`, SHA-256 `51bcc74ea5edaaf3d0782197133e614746227c3a76c683961cdecdb76f2f4738`) leaves complete component/fixed/event consumer construction open. Native row freshness and numeric maps establish neither source classification nor binder strategy. No new source-qualified counterexample is asserted.

`InferenceSoundness`, source Call/shared-witness, full Generalize allocation, source/native correspondence, effect hygiene, parent, principality, termination and production remain **OPEN**. Independent F1/FK1 and foreign-continuation quantifiers remain intact. Approved Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization remain the governing operations.

Mutual TODO `R16-NATIVE-JOIN-1` (Luna/Cargo owner): provide frozen one-attempt argv/environment, versions, complete stdout/stderr, status/resources and byte hashes. Falsifier: load/build failure, absent/wrong same-graph index or ports, incorrect scope/relation/use, or next failed guard. After Luna ACKs rev1 and freezes logs, resume within the original grant for rev2 mapping. TODO `R16-SOURCE-CALL-1` (Luna/source owner): derive the quantified original Call/telescope allocation law from actual constructors/consumers, or provide a source-qualified counterexample; a successful fixture cannot supply it.

Checks/resources: read-only source/document inspection and SHA-256 authentication only; zero Cargo/tests/build/metadata/Lean/Git/checker, zero descendants. Total assignment grant 600s, stage1 cap 300s; exact launch-relative elapsed/CPU/RSS unavailable, **UNKNOWN**. Stage2 must use only the remaining original grant, with primary budget accounting retained. No background process; all new/scratch paths: only this leased handoff. Revision 1 frozen; **WAITING / writes stopped**. Pending independent review and Luna integration.
