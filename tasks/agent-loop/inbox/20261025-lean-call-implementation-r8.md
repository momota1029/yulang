# LEAN-COMPLETE-CALL-20261025/r8 implementation repair handoff

Sprint-ID / contract revision and SHA-256: `LEAN-COMPLETE-CALL-20261025/r8`, `2c0deecaa520a208951ed73af941e3b92e440530cdc78c3f27d6befeaf8e3a88`.
Assignment-ID / handoff revision: `LEAN-COMPLETE-CALL-20261025/r8-IMPLEMENTATION` / **1**.
Parent gate / original theorem and scope locator: checked typed Call representation and actual Call execution seam under r8; exact P/Q/B claims remain gated in the frozen contract. Full Yulang semantics/type inference, original inference A/B, source/native correspondence, principality and termination remain OPEN.
Baseline / direct dependency hashes: baseline `dc6088c8e0b00248f0c14043f3cdb1e129ce6b92`. Contract and direct frozen code/toolchain dependencies rehashed unchanged: `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; `CoreComposition.lean` `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c`; `YulangClosure.lean` `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`; `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `lakefile.toml` `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; `lake-manifest.json` `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
Role / actual worker ID / current session / launch or resume receipt: Luna/high implementation repair / `/root/call_implementation_r8` / current session and runtime launch metadata not exposed to this worker; assignment received from `/root` in this turn.
Requested model and effort / observed model and effort: `gpt-6-luna` / high; observed model and effort UNKNOWN (no runtime metadata exposed).
Exact leased paths / authors: `CoreSyntax.lean`, `CoreSubstitution.lean`, `CoreExecution.lean`, `ControlSyntax.lean`, `ControlTyping.lean`, `ControlComposition.lean`, `CoreControlBridge.lean` under `notes/theory/lean/YulangClosure/`, plus this handoff only. No descendants. Changed paths are `CoreSyntax.lean`, `ControlSyntax.lean`, `ControlTyping.lean`, and this handoff; the other four leased source files are unchanged.

## Outcome

Outcome class: **implementation repair candidate; compiler check pending; proof and source/native correspondence OPEN**.

Repaired the listed r7 elaboration causes while preserving the candidate's represented operations and typing claims:

- Removed the unused `DecidableEq` derivation from `TypedCall.CallType`, whose `Original.Ty` payload has no decidable equality.
- Declared `PortPath` before `ViewOccurrence`, and declared `Adapter` before `InterfacePlan`.
- Renamed reserved `instance` binders/fields to `opInstance` consistently in Call syntax and typing declarations.
- Separated the `Function` syntax constructor from Prop-valued `FunctionTyped`: function syntax retains mode, receipt, argument/body/result types, body and result consumer; `FunctionTyped` retains the same body typing and adapter endpoint premises. The Call transitions that attach the receipt and enter the lambda carry the matching `FunctionTyped` premise, keeping the receipt-before-entry order and its typing requirement.
- Corrected `requestScope`, `requestExpose`, and `finishRequest` payload binders to `TypedCall.Value`, matching the request syntax and preserving the operation instance and saved continuation.

The source/formal sequence in the candidate remains Call start into Scope, outer-to-inner wrapper peeling with delayed argument adapters, receipt attachment before Value/Computation entry, body and declared-result consumer, inner-to-outer result adapters, and normal Scope return. Existing Call metadata, observed Views, world operations, Fail cleanup relation, Req/Fail constructors, and literal suffix fields were not edited.

## Parent/source/native correspondence and boundary

The r7 representation and its owner-path history were inspected and reused as the starting point. The r7 receipt (`tasks/agent-loop/sprints/lean-complete-call-20261025-r7-outcome.md`) reports `CoreSyntax.lean` failed under pinned Lean with 33 elaboration/type diagnostics, exit 1 in 3.55s; it reports no dependent module check and no proof or review. Its failure is not a semantic counterexample or theorem evidence. The prior implementation handoff at `tasks/agent-loop/inbox/20261025-lean-call-implementation.md` preserves the intended transitions and admitted Req/Fail behavior; it is historical evidence, not acceptance.

The governing operational source was inspected at `docs/yulang-operational-type-safety-ja.tex` §§ “順序付き bind と request の伝播” and “call の入口と adapter” (around lines 337–400), and the corrected continuation note was inspected. Those sources specify a value payload with response-typed continuation, outer-to-inner wrap peeling, delayed argument adapter, receipt before force, mode-dependent entry, result adapters and Scope behavior. This repair aligns the previously ill-typed payload binders and leaves those represented steps intact. No source constructor-to-frontend constraint generation, compiler propagation, native execution, or source/native theorem was added or checked. Decorated-plan authenticity, full source View/eligibility/current-world coverage, all foreign-tail behavior, and the full parent remain OPEN.

No provisional source instrumentation was added. There is no cutover or production claim. P/Q/B remain unissued to this worker; Luna must first run the serialized checks and adjudicate the actual-execution/nonvacuous-Bad seam.

## Frozen artifacts and checks

Artifact SHA-256 at handoff:

| Artifact | SHA-256 |
|---|---|
| `CoreSyntax.lean` | `c6330ad1cf8a17b0a35f9928af82478830113f4afeb423042f74e84b0ece1916` |
| `CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1cff4497661aec68c384871f0eac0e32c34166d9ea489667791d21ce67d988d1` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |

Checks performed: inspected r7 outcome and implementation handoff, inspected the governing source sections and current declarations, scanned the leased Call declarations for remaining reserved identifiers and old lambda constructor uses, and computed the artifact/dependency hashes above. **No Lean, Lake, tests, Cargo, native checks, Git commands, or proof-hole scans were run**; Luna owns the serialized compiler verification. The hashes freeze candidate bytes only and do not establish elaboration or theorem validity.

Prior evidence reused: r7 source representation, its transition/typing history, frozen r8 contract and unchanged r6 dependencies. Prior evidence rejected for this result: the failed r7 Lean attempt establishes only the reported elaboration failure; r7 handoff claims and green workflow-state checks do not establish source reachability, compilation, P/Q/B, or semantic approval.

Budget: assignment maximum 1,200s including preparation. Actual elapsed active time is UNKNOWN because no monotonic launch/elapsed receipt was exposed; no verification process was launched and no other stage grant was spent. This worker cannot certify the effective model or exact elapsed budget. No scratch or generated paths were created.

Mutual TODOs: Luna — run the frozen serialized Lean checks in the contract's dependency order, record the first exact diagnostics, and determine whether actual Call execution/nonvacuous `Bad` exclusion is connected before issuing P/Q. P — only after that gate, prove `call_context_plug_typed` and inversion from these frozen hashes. Q — only after that gate, prove transition classification using P and actual substitution; stop on any missing constructor or metadata/world/suffix correspondence. B remains gated on the exact checked Proposition A declaration/hash.

Next related in-envelope step: Luna's serialized representation check and execution-seam adjudication. No semantic choice is asserted by this handoff.

Worker state / stop: **STOPPED; source writes ceased after this handoff was frozen.** No descendants, pending writer leases, disposable scratch, or generated outputs. Commit-ready milestone: no; compiler checks, proof stages and independent review remain pending. Handoff ID/revision/hash: `LEAN-COMPLETE-CALL-20261025/r8-IMPLEMENTATION`, revision `1`; SHA-256 to be recorded by Luna after freeze.
