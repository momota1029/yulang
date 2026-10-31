# R88 source handoff, revision 1

Outcome: **NO_SAFE_CODE_SLICE**. Claim class: bounded source/native evidence and exact missing premise; no theorem closure or source-qualified counterexample. Review: pending fresh independent review. Writes stopped after this revision was created; its SHA-256 is supplied separately to the primary.

## Identity, authority and frozen inputs

- Sprint: `SOURCE-SCOPED-JOINT-LIFT/20261031-R88`, contract revision 1, SHA-256 `e6adf9efbcea3d07aa3b419c52c5ec878d3852afa3231047cb1e7f2a0fa8304d`.
- Assignment/author: `/root/r88_source`; parent/delegator `/root`; no descendants or contributing authors. Session: R88. Requested lane: Luna/high in the contract. Actual runtime model/effort: **UNKNOWN**; no runtime tool receipt identifies them. A role description or requested setting is not an observed setting.
- Primary-dispatched checkpoint baseline: `8fd0da905449b5f4214f0ec5aa487075c03060a9`. Contract/manifest input-baseline field: `93fe63707d3a889f09284088413e2fc233aae468`. The explicit file hashes, rather than an assumed equality between these commits, govern this report.
- Manifest SHA-256: `239497900445ae2b3b8e546f6f080db1bf1ec7dc52b9ee1b28bbede4f3c70353`. All **26** listed working input sizes and SHA-256 values matched at entry and recheck. No manifest-pinned input was changed by this worker.
- Only write lease/output: `tasks/agent-loop/inbox/effect-permission-source-joint-lift-r88-source.md`. No scratch, cache, generated output, `/tmp`, worktree, compiler, configuration, manifest, question or shared-record writes.

Governing sections: original preservation manuscript §§1, 5, 7; birth-level decision §§2–4, 6; Source-Generalize decision §§2–4 and its construction §§3.1, 3.3, 4, 5.1–5.2; top-level principles §§1–5. The immutable-birth induced-graph qualification remains selected. Numeric levels do not identify scopes; fresh use is not extrusion. Complete Call/effects, actual provider/capture identity, Shared witnesses and lawful independent-use coverage remain required. The Source-Generalize decision explicitly grants no implementation authority.

Direct hashes used in the argument (SHA-256):

| Input | Hash |
| --- | --- |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `OriginalPrincipality.lean` | `c9d214cd086aa1fbdf8f471e7b52c8cccddaa971fc68a8bb0956c9539d098dc7` |
| `OriginalSourceValueEntryAdmission.lean` | `3dc218f9d6623192d7d85c6f5be14f0fddbe833b19ede467c75647a5833205dd` |
| `OriginalExtrusionWork.lean` | `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58` |
| `OriginalExtrusionFibers.lean` | `15bb4ebc67a22f4bd3af584e8377dec210963f7cbba43e6072c82b5f2d5a8800` |
| `OriginalScopedClosure.lean` | `b316a5e18a14b4c9750cc97f294aea824ce6b0a704fc67929fa4a016e94ebeab` |
| `SourcePrincipalTransport.lean` | `ab86c4448dcddcb5e20ef1495e317c4d0fc04ad0ff52c4323779d12f5fde33ee` |
| original preservation manuscript | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| Source-Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| birth-level decision | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| R87 outcome | `72e2fc795a8d7e10c104ad2fc902f884165d1355dccb37476da264267c582816` |

The full paths and remaining authority hashes are in the authenticated manifest. Rust basenames above mean `crates/yu-solver/src/`; Lean basenames mean `notes/theory/lean/YulangClosure/`.

Baseline distinction: at dispatched commit `8fd0da905449...`, the `candidate_context.rs` blob is 265,078 bytes / `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`; the admitted manifest instead freezes 265,778 bytes / `a6e8bd...`. The read-only diff adds borrowed `use_origin_index`, `use_origin`, `use_source_drain` to `CheckedBoundEmission`/`InternalUseRootEvidence` and their construction. Narrow `git status` still marked that file modified. These are admitted input bytes, not this lane's edits, committed source laws or new implementation authority. The receiver and three specifically requested theory files agree with their `8fd0da...` blobs. Observed HEAD during the check: `1d8f8231c56b2d161681c6b2db5ac8704334aaf5`; the report does not substitute that HEAD for the dispatched baseline.

## Actual source construction and first unmet goal

`OriginalSourceGeneration.sourceRules`, lines 111–123, computes an App from raw source. Under its **one** `existsE ⟨site, viewLogic, 0⟩`, it retains descriptor formation, whole inert argument compatibility, complete Call certificate, source Call incidence and callable image; the singleton-formal clause appears only when `singletonFormalCall` computes true. It also checks `callee.returnedValue` against this App's descriptor and `callableImage` against synthesis. Both child source trees remain present. `Kernel.atom`, `Kernel.admitted`, local checking and conversion are semantic premises, not consequences of creating those atom names.

The first missing source/native incidence can be stated without inventing a replacement rule. For an actual native slot-0 demand with call index `c`, obtain the original source App site `q`, context `Γ`, callee/argument sites and complete original environment `E`. After the App's single admitted ViewLogic choice, establish in that **same** environment `E'`:

```text
Local K E' (.atom (atom .sourceCallIncidence q Γ [calleeSite, argumentSite]))
Local K E' (.atom (atom .completeCallCertificate q Γ [calleeSite, argumentSite]))
```

Here `K` must interpret the original independently established local source laws. The remaining App atoms, both checking goals, child derivations and the exact native coordinate/pair map must use these same operands and telescope. The missing result is not a request to assume these propositions: it is a construction from the actual owning source rule, relating its complete tuple to `ApplySourceInput.introduction`, the retained extrusion occurrence and every actual value/effect parent/copy pair.

Exact first native seam: `InferenceSession::candidate_context_seed` (`candidate_context.rs:3794–3857`) consumes `batch.candidate_calls.calls[c]`, its `ApplySourceInput.introduction`, and checking slot 0. It creates `ScopedDemand { original_call: c, use_instance: 0, root: introduction.demand, output_scope, input }`. The current in-scope checked source join is `InventoryPackage::capture` (`candidate_receiver.rs:4613–4677`): it authenticates owner-local `Form::Apply`, expression index, HIR ownership, callee/argument indices and checking/cause identity. That join does **not** produce either Local proof above, an `OriginalScopedClosure.Position`, or a mapping from native rows to original source binder occurrences.

Responsible owner: the primary's source/native App/Call construction bridge, specifically the owner that constructs `candidate_call::ApplySourceInput`/its `introduction` and registers the generated source-checking occurrence; `candidate_context_seed` is the first inspected consumer. The complete Call law is source-constructor premise L2, with actual L1/L3/L4/L5 evidence where used. The current Rust producer outside these two files was not authorized for inspection. Historical §7 pointers to `candidate_source.rs`/`shadow_apply.rs`/`candidate_call.rs` are owner locators, not freshly verified current-source facts. Luna must pin their actual constructor definitions before an implementation lease can follow.

Derivation of the obstruction: reconstruction requires `Satisfies K E (Build Γ source)` and inverts to the Local premises above. Native seed/inventory operations return relations, metadata or checked borrowed coordinates. No inspected operation supplies the missing original local interpretation and source-telescope incidence. Thus the reconstruction theorem cannot presently be instantiated from those operations. This is a bounded failure to establish a premise, not proof that no implementation can retain it, and not an arbitrary-Kernel counterexample to Yulang.

## Trace through effects, extrusion, publication and uses

| Stage / inspected owner | Actual retained construction | What remains unestablished for one original telescope |
| --- | --- | --- |
| Source App / `sourceRules` | Complete atom family and returned-callee/value and computation checks under one ViewLogic binder | Concrete interpretation of the complete Call and incidence atoms for the actual native generated demand |
| Demand / `candidate_context_seed` | Slot 0 records the five fields above; slot 2 applies `release` to the argument's computation scope | Original scope/dependency tree, returned provider/current receiver/receipt, inert whole carrier and designated consumer incidence |
| Function ports / `candidate_function_port_admit`, `candidate_context.rs:3925–3988` | Argument and ArgumentEffect use Swap; ResultEffect and Result Preserve. It checks the parent negative Function root, consumes the demand, uses `stamp_input(demand.input)` for ArgumentEffect and `protect_body(demand.output_scope, demand.input)` for ResultEffect | Interpretation as complete original Call effect evidence, lower/upper support, annotation permissions, capture/attachment/continuation witnesses at the same source event; four ports alone do not supply it |
| Whole-value rewrite / `candidate_context_value_rewrite`, 3902–3924 | Root follows the rewritten upper negative Function; retains sources and records Derived | A copied endpoint's original source binder/semantic incidence |
| Bound / `candidate_context_bound_for`, 4317–4356 | Exact raw bound, inherited post-check context, scoped payload, source set and Derived link; the checked allowance boundary has its own retained DAG | Source law validating that boundary and all dependent effect witnesses; source-set IDs do not encode that law |
| Parent/copy / `CircuitEvidence`, 1379–1408 | ParentCopy refers to an exact parent index and verifies kinds/polarity; Extrusion/EqualityCanonicalization authentication remains unavailable here; completeness always includes filter, readiness and dependent-observation gaps | Approved immutable source Value birth and induced-graph SCC proof, actual origin/receiver and pair-to-source incidence. No such result follows from endpoint representatives |
| Extrusion theory / `OriginalExtrusionWork.Operation`, `State.retain` | Operation carries a supplied `qualified : Bool`; retains copy, parent, polarity, target and operation; queues that parent if qualified | Construction equating the supplied Bool with approved source-birth qualification; source scope/evidence is explicitly outside this local Work projection |
| Fiber theory / `OriginalExtrusionFibers.transportKey`, `transport_key_exact` | Computes native bound pair, representative renaming, parent post-context, source set and remapped demand root. Preserves transformer and four non-root demand fields | Native extraction/readout validity and semantic source telescope. “Source” lookup here is a retained native relation, not source-rule admission |
| Residual publication / `publish_authenticated_residual`, `capture_native_publication_call`, `candidate_receiver.rs:3152–3220,3448–3563` | Forwards residual effects through `constrain_live_effect`; records cuts, exact physical slot/admission/emission, source-drain and ancestry; observation may be unavailable | This is Catch residual bound publication. It supplies no source scheme installation or Source-Generalize fixed/template/dependent-field classification |
| Original closure / `OriginalScopedClosure.allocate`, `prepare`, `openPublication` | Computes rule positions with full telescopes; copies description-frame prefixes; shared/event references retain owners. Opens only the actual named publication after origin/site checks, restores original environment fields | The module explicitly leaves eligibility, semantic originalNewInstance, grafting/fixed-dependency closure and all-valid-view extension separate; no inspected native installer constructs this closure |
| Fresh native use / `begin_use`, `candidate_context_fresh_transport_scoped`, `authenticate_replay_ancestry` | Nonzero use counter; exact FreshUse from/to witness, supplied ScopedFlow, retained sources and attachment. Authentication checks unique FreshUse/Replay/port edges and exact effect transformers | Counter/edge identity is not source `new`/alias partition or whole-component allocation. Scoped mode requires caller-supplied flow. Source-Generalize §5.2's one frame per independent use, fixed Shared base and EventProof incidence remain unconnected |

`SourcePrincipalTransport` constructs the actual raw source `top = lambda h. let rec f = lambda x. lambda y. {first = h x, next = f {a = y}} in f`. Its theorems calculate both complete App rules, recursive f's monomorphic binding and the second field under h's `executionE ⟨16, returnRebind, 0⟩`. They retain h's returned-callee endpoint `⟨17, returnedValue⟩` through arbitrary frames. `h_return_supplies_current_receiver` uses the supplied actual Return value/provider; it explicitly assigns no native copy occurrence. It supplies no admitted birth-qualified nonempty extrusion event. This source is therefore a source-side anchor, not a native execution witness or counterexample.

`OriginalSourceValueEntryAdmission.source_receipt_record` and `presented_receipt_fields` retain the constructed receipt and carrier/view. `independent_receive_fields` leaves current/path/consumer/incidence as the independent template's fields; `receipt_decoder_uses_supplied_current` does not admit the receipt. Thus a native callback/drain receipt cannot silently replace the source Invoke/Receive-before-Force law. `OriginalSourceInterpretation.CallInput` and `Challenge` retain value/root, event, context, continuation, carrier/root/view, receipt, path, consumer and incidence; `Inputs` keeps receipt-precondition, actual typed path/context, actual execution and checked-observation obligations explicit. No field equality above removes these duties.

`OriginalPrincipality.joint_descent_iff_fiber_constant` requires the canonical transport and proves descent iff the **one whole valuation** is fiber-constant. `quotient_uses_complete_on_fiber` additionally requires finite store bounds, anchor preservation, use bounds, actual solved constraints and FiberConstant. These are conditional algebraic results. They supply no source law that constructs such a strategy for all birth-qualified Apps, and changing internal assignments lawfully remains permitted by the original parent.

## Evidence limits, checks and resources

Method: source-constructor inversion, record-field and call-site tracing, cross-check against the fixed scoped source declarations. No executable transition model, oracle, search, seed, mutation or theorem check was run. Reference independence is limited to reading the separately defined original source rules and the actual native consumers; this is not an independently implemented source-semantics oracle. Both sides still need the same original local laws. There is no minimized source counterexample in this handoff.

The private receiver envelope matters: `assemble` (2963–3122) selects exactly two module definitions, an annotated retained Computation formal, one operation and a two-arm shallow Catch with unit payload/wildcard continuation. It excludes nested bindings, annotations on those definitions and unrelated expressions. `execute_receiving_assembly` (5473–5599) requires one module use and explicitly does not populate intrusion `active_roots`/`uses`. It is neither the full source domain nor a witness of the R88 qualifying event. Optional module-Name alignment does not discard the other collected calls. Borrowed reification, endpoint encoding, provenance round trips, physical readers and ancestry readers remain observations of this owner; their success does not prove source constructors.

R87 outcome is accepted only for its recorded bounded finite reader correspondence. Its native extraction, whole-crate coverage, pointer/shared-payload authentication, Saved.otherChecks equivalence and original A/B remain open. No R87 PASS is used as an App/Call local law. The admitted dirty fields retain a selected origin/drain row; they do not change this conclusion.

Commands/checks already run: bounded `rg -n`, `sed -n`, `cat` over the named input/rule/skill files; a read-only Python `pathlib`/`hashlib` manifest check and recheck (26/26 size/hash matches); `git rev-parse HEAD`, `git show` for five named baseline blobs, narrow `git diff` and `git status` for the two read-only Rust paths. All returned exit 0. No tests, Rust compiler, builds, Lake, Lean, installed environment changes or heavyweight processes. No all-source enumeration was attempted; patterns do not prove whole-crate absence.

Resource envelope: 1,000 seconds active source lane; heavyweight invocations 0, search/model invocations 0, child processes for proof/build 0. Exact total worker wall time, CPU and peak RSS are **UNKNOWN** because this lane did not receive a launch timestamp or resource monitor; per-command reported shell wall times were below one second. Observed UTC during final source checks: 2026-10-31 14:48:00. The primary owns the launch-to-stop elapsed accounting. No budget reset is claimed.

Unverified: production App demand producers, actual birth/SCC constructor and native extrusion implementation, source/native scheme installation and full lawful-use allocator outside the pinned two-file read lease, whole-crate transitions, all source constructors' concrete local laws, the joint lift, standalone Lean imports/axioms, global soundness/principality/progress/termination and production. The broader parent remains OPEN. No source case is removed by this bounded coverage statement.

Recommended next action: Luna should admit one exact source-owner evidence packet at construction of `ApplySourceInput.introduction`, linking the original complete App/Call/effect tuple and telescope to the generated checking occurrence and retained extrusion pairs. Pin the external producer definitions first; require source birth qualification and Source-Generalize publication/use incidence as explicit dependent evidence. Retaining IDs or enlarging the finite reader model again leaves the first premise untouched. No Rust slice can yet be justified from the inspected approved source laws and path.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/effect-permission-source-joint-lift-r88-source.md` only.
- Baseline SHA: `8fd0da905449b5f4214f0ec5aa487075c03060a9`; manifest input baseline `93fe63707d3a889f09284088413e2fc233aae468`; exact frozen dependency override for `candidate_context.rs` recorded above.
- Dependency hashes changed by this worker: none; all 26 manifest dependencies matched on recheck. No compiler path is included in this packet.
- Review status: research-only, fresh independent review pending; no self-certification. Parent application: fixes the first unmet incidence and its owner; does not discharge A/B or authorize implementation.
- Checks already run: read-only hash/size validation, source/declaration tracing, exact baseline blob and narrow diff/status inspection. No tests/build/Lake/Lean.
- Proposed one-line checkpoint message: `research: locate R88 complete App to scoped extrusion incidence blocker`.
- Shared-record deltas intentionally left for Luna/curator: record `NO_SAFE_CODE_SLICE`; preserve original A/B and effect/source-native gates OPEN; distinguish residual bound publication and native FreshUse evidence from source scheme/allocation; retain the baseline/dirty-input distinction. No central state, index, authority or question bundle was edited.
- Worker state: STOPPED WRITING for submitted revision 1; no descendants or unresolved generated-output leases. This file is frozen for review; any later repair requires a new primary-directed sequential revision.
