# c2 typed native call — independent compiler review

Revision: 1  
Sprint: `c2-typed-call-occurrence-correction-20261017`, contract revision 3  
Reviewer: `/root/c2_typed_call_compiler_review`; no descendants  
Observed model/effort: UNKNOWN / UNKNOWN  
Launch: current assignment, first observed clock 2026-10-17 04:15:50 UTC; work began shortly before that observation.  
STOP: 2026-10-17 04:16:49 UTC; approximately 80 seconds allocation elapsed (59 seconds since first observed clock), below 90-second cap.  
Scope: static independent compiler/source review; receipt is the sole output lease.

## Verdict

**CLEAN within the stated conditional source/native correspondence scope.** No BLOCKING, major or minor compiler-correctness finding in the corrected equations or proof. Parent result remains PARTIAL: original F2 admission, IF(g), complete B_in, VIEW, CHECK, F1/FK1 and original A/B remain OPEN. This review approves no semantic rule, production change or code.

The correction repairs the cause of the prior false inference: it replaces the alleged argument-to-Demand-argument constraint with the actual whole-call constraint and withdraws admission. It does not conceal the wrong polarity by dualizing the retained child or by adding a downstream semantic predicate.

## Independent evidence and adversarial paths

- `candidate_source.rs:980–1050` reads the exact Apply child IDs, uses those children's endpoints in the recipe and source registration, and creates checking slot 0 plus its occurrence-derived cause. Root ownership is the actual registration owner. Renaming the source g or receive does not affect this index/occurrence-directed result. No selected numeric root is needed.
- `shadow_apply.rs:1560–1580` checks registered recipe/input links and operands; `1585–1655` constructs `callee+` and `argument+`, embeds the latter in the negative Function Demand, and retains native operands before admission. `1658–1674` admits `(callee+, Demand-)` at the recipe occurrence's slot 0. `1680–1743` generates the separate effect slots 1 and 2. Thus the proof's native port equalities and whole-call pair match the owner implementation.
- `candidate_call.rs:437–532` checks the actual HIR Apply children, occurrence/cause, owned occurrences/scopes, negative Demand children and positive argument port. A forged different slot can satisfy its occurrence-only check; it is the constructor, not the observer alone, that establishes slot 0. Proof §1 explicitly states that limit. Likewise source/native authentication uses the constructor provenance premise; observation alone is not an arbitrary forged-record completeness theorem.
- `lib.rs:12550–12554`, `12644–12720`, `14179–14220` require actual positive and negative Function endpoint tags, then reverse argument and argument-effect children while preserving result children. With actual parent `P+ <= N2-`, the argument obligation is `arg(N2)+ <= arg(P)-`. A positive callee row alone supplies no such P. Memo/work dispatch and resource failure do not prove child satisfaction. Proof §3 retains these premises and limits.
- Alternate path: `candidate_source.rs:1002–1004` rejects a local-name callee in the scoped experiment. Therefore successful construction/reachability of this c2 cannot be inferred merely from the displayed source. Proof §1 explicitly conditions the constructor theorem and disclaims whole-source acceptance/reachability. This is a bounded theorem, not evidence that this exact source currently succeeds through every candidate route.
- Alternate path: graph effects disabled leaves no invocation row and a source-registered call fails at `shadow_apply.rs:1618–1620`; proof §2 excludes treating the fallback as an authenticated source call. Allocation failure, later effect admission failure or incomplete decomposition similarly lies outside the successful-constructor/completed-dispatch premises. No failed partial state is promoted.
- Existing tests were read, not run: `shadow_apply.rs:1870–1925` distinguishes original Demand/invocation/application/argument effect identities and rejects corrupted directional records; `2559–2617` retains actual formal-row identities in both whole-call callee and Demand argument. These support ownership distinctions, not semantic admission or this exact source's reachability.

Authoritative check: inferred Function call views §2 preserves source slot/path ownership and prohibits pending Q from creating admission. The corrected source §§2–4 and proof §§4–5 obey that clause. Top-level inference principles §§1.1 and 4 distinguish source constraint construction from execution and preserve accepted-state safety without requiring full failure rollback. No extra rollback theorem is asserted. Prior graph/Bind and identity-telescope mathematics is reused only for the same retained suffix and an already well-formed/typed telescope; it installs neither IF(g) nor a semantic interface map.

## Frozen bytes

All twelve input paths were independently rehashed. Ten unchanged pins match the contract. The two source outputs match their explicitly versioned revision-2 replacement pins; historical predecessor hashes are not represented as current bytes. Contract revision 3 changes review coordination; the proof/handoff's recorded revision-2 hash is historical provenance, not a claimed revision-3 hash.

- Source correction: `a78c3b32db064e3e6add46daeb7395703fe453fb6aba74ba9d98ce82ed409d25`
- Source handoff: `3bc79093b819f2de7029b81136bbfed0a3b9ef727acf68cb5c87696b184e9be4`
- Proof artifact: `725c14759f92b85203b5d22894b0de1da95732448b50f0718a8879ed56243aed`
- Proof handoff: `923f792a915d8e3a95adf4d563f43c59f5cc99ff5ddf60d9ec07e6f1a7110b64`
- Reviewed contract revision 3: `aaaff21bda20de6288fd660356e6fcb63460e76bae2d239b662746664cf11adf`
- Constructor/observer/decomposition source hashes match proof §6 and the contract: shadow_apply `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`; candidate_call `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1`; candidate_source `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`; lib `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.

Checks: static source/spec/test inspection and byte hashes only. No test, build, probe, compiler/runtime execution, source/proof/contract/state modification, Git mutation or semantic adoption. No correction required within this packet. Remaining source-admission and complete-carrier owners remain exactly proof §5's TODOs. Worker STOPPED; writes stopped; no descendants or unresolved child leases. Sequential spec review and Luna adjudication remain pending.
