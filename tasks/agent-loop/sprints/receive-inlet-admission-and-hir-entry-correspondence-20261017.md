# Sprint receive-inlet-admission-and-hir-entry-correspondence-20261017 — compare the first inlet clause and runtime identity route

Status: READY / Luna-approved for bounded proof comparison and source correspondence  
Branch / baseline: `research/simple-sub-intrusion` / `14a830e6f`  
Contract revision: 3  
Authority: parent goal and user-authorized autonomous drafting/review workflow; no semantic adoption or compiler-code lease.

## Original outcome and success evidence

Parent Goal remains **型推論と実行器が証明込みで実装できるまで続ける**. The preceding sprint is REVIEWED-PARTIAL with a frozen SAT/RG candidate and a read-only runtime trace. Its fresh compiler, spec and architecture reviews completed; the one compiler source-locator finding was repaired and delta-reviewed. Original FORWARD-FIRST-CALL A/B, source/native T/MODEL and production gates remain OPEN.

This sprint resolves one comparison only: whether the original c2 inlet requires the candidate SAT clause's universal designated-execution typing, especially for a carrier whose actual Lambda enters through Value versus Computation. Compare both inclusions separately against the original selected admission/entry meanings, with complete dependent guards and actual source premises. Produce a derivation, an authentic source-qualified separating case, or the exact missing original admission clause that prevents comparison. An arbitrary descriptor countermodel is not a source-qualified c2 case.

In parallel after the proof output freezes, trace whether the selected `my apply f = { my step x = f x; step }` runtime entry path can be accounted for from retained HIR identities alone through closure creation, alias/capture, invocation and saved-context restoration. Either prove this narrow annotation-derived Value/Computation correspondence for the selected source path or identify the first broken identity join. This can establish that candidate evidence transport is unnecessary for this runtime-only classification; it cannot establish semantic Pure/Handler, source typing, full inference/runtime plan validity, or original c2.

## Sequential lanes and exact leases

### Original inlet versus SAT admission — Astra prover, maximum 720 seconds

Write:

- `notes/theory/2026-10-17-receive-sat-admission-comparison.md`
- `tasks/agent-loop/inbox/20261017-receive-sat-admission-comparison.md`

Start from original F2/xi and frozen SAT/RG candidate. State both inclusion goals with the original binder order and complete tuple. Inspect selected carrier/entry and contextual-membership laws. Ask whether independently admitted retained carriers already satisfy the universal `T_B` condition at the original incoming ports. Attempt both directions; preserve independent admission, licensed non-source observations, pending/request/divergent/future branches, all actual providers and original contexts/worlds. Do not define the inlet as SAT, restrict to successful/source executions, infer Pure/Handler from Value/Computation or Unit, or use provider acceptance as admission.

Keep RG2, full guard inventory, arbitrary joint descriptor embedding, arbitrary graft coverage, complete R/IF, WF_Dec, membership, VIncl, inlet compatibility, CIncl, ambient joins, F1/FK1 and parent closure distinct. Apply any result to the exact predecessor obstruction and name the first still-open owner.

### HIR-owned runtime entry correspondence — Luna/high, maximum 300 seconds, only after Astra STOP/freeze

Write:

- `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`
- `tasks/agent-loop/inbox/20261017-hir-owned-runtime-entry-correspondence.md`

Trace the same named formal/Lambda identity from HIR `IdentifierPattern` and local owner records to `RuntimeProgram` Lambda instruction, runtime Closure capture environment, Parameter binder/lookup, local aliases, and saved/restored frames relevant to the selected returned `step`. Determine whether each consumer uses source identity and captured environment consistently without importing CandidateInference. State the exact runtime-only claim and all source premises. This lane is read-only and cannot change runtime behavior.

## Frozen dependencies

All pins are current bytes at preparation and must be recomputed before reliance. A mismatch returns to Luna.

| Input | SHA-256 | Use / limit |
|---|---|---|
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` | Original A/B and F2/xi parent; stays open. |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | Original F2 direction and open inlet fields. |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` | Selected constructor scope/entry laws, not assumed c2 specialization. |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` | Selected Value-entry proof package; only within its true premises. |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` | Complete membership and independent admission separation. |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` | Selected complete Call-input admission/observation law; exact theorem premises only. |
| `notes/design/2026-10-17-receive-role-indexed-inlet-introduction.md` | `7716a71d6bf6f5212bd455e1a3959569748e558238d0a164649ec1c57d92b72c` | Unselected SAT/RG formulas and exact SAT2/RG2 gaps. |
| `tasks/agent-loop/inbox/20261017-receive-role-indexed-inlet-introduction.md` | `70dc1e462150474fa7f404bb4aa9aa844825b77b985e9187fa80d74ac4f97138` | Frozen candidate handoff and owner TODOs. |
| `notes/theory/2026-10-17-value-entry-formal-provenance-through-local-use.md` | `76855d9330a9b5404dfa83bffc4c033dea4c40763b8104bda04849474278deec` | Revision 2 trace, source correspondence lead only. |
| `tasks/agent-loop/inbox/20261017-value-entry-formal-provenance-through-local-use.md` | `a0ace650412579127e2a210b6fba5b22603d0f9e3818564ef3240fd605eba3d0` | Frozen revision 2 handoff. |
| `notes/theory/2026-10-17-receive-sat-admission-comparison.md` | `956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1` | Frozen Astra comparison; both SAT2 inclusions remain open. |
| `tasks/agent-loop/inbox/20261017-receive-sat-admission-comparison.md` | `e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822` | Exact VIEW/CHECK owners and falsifiers for the sequential source lane. |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | Named formal construction, Lambda wrapping and local identity. |
| `crates/yu-hir/src/source_identity.rs` | `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2` | Named/inline formal source origins. |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` | Structural local fresh-use maps; no runtime authority. |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` | Annotation-derived Lambda entry and runtime instruction. |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` | Closure capture, binder lookup, request/save/restore consumers. |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` | Experimental execute's existing inference/runtime boundary. |

## Resources, review and stop conditions

Fresh envelope: **1500 seconds** — Astra 720; source correspondence 300; compiler-referee 120, spec-auditor 90, architect 90; coordination 60; reserve 120. Authors are sequential; reviewers are fresh and sequential after both outputs freeze. Existing three UNKNOWN legacy reservations remain quarantined. No worker in this sprint writes code.

No tests, builds, probes, compiler/runtime execution, fixtures or expected-output edits. No semantic adoption, compiler-code authority or production promotion. STOP at either lane cap, an authority/dependency mismatch, an authentic counterexample requiring changed scope, or completion of the bounded result. Unused time retires. Luna alone updates state, reviews and integrates explicit paths.

Success is an original-source-qualified SAT comparison result or an exact missing admission law, plus a narrow runtime identity correspondence or its first actual broken join. If the SAT comparison remains ungrounded, do not restate the same obstruction: identify the exact owner/input needed next. If HIR identity suffices for runtime-only entry, record that this retires only the candidate evidence-transport dependency for that selected experimental runtime; it does not authorize a code patch or close theorem gates.
