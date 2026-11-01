# R155 independent compiler review

Disposition: **PASS for HOLD / NO_PATCH; BLOCKING for applying the residual input.** No source integration or production authority follows.

Reviewer: fresh independent compiler_referee, assignment /root/r155_review. Read-only review; no descendants. Initial assessment used the immutable input, committed target/dependency blobs and governing policy before consulting producer explanations.

## Exact reviewed identities

Baseline: `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`.

| Artifact | SHA-256 |
| --- | --- |
| R155 contract | `1fb5c38fb14f6f11c1ac8d26930168f2b7bf0422948e4f79c0fcd3b916bd1309` |
| immutable input patch | `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f` |
| implementation handoff | `66b2c471f0d32c646cd55d5b8ce0ecac1b8f215b3e1bfa32ef59920b0dcf318f` |
| proof handoff | `29a9099a8f0cccae1658ee458e671ef75216b41db1e286a8165f13822ff2ad00` |
| NO_PATCH marker | `4afc0c7a18ce6112446c8be8565df142c4346debce3d3721edb25971397d1ccd` |
| baseline candidate_scheme.rs | `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2` |
| reconstructed target scheme | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| candidate_effect.rs | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| candidate_receiver.rs | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| candidate_context.rs | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| candidate_source.rs | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| lib.rs | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

All seven source hashes were independently computed from read-only committed blobs. Every context/deleted line of the sole hunk was checked in memory at its exact baseline position; no offset/fuzz or patch application. Reconstructed target equals the contract hash. R152 candidate/source/proof/review/outcome and R153 integration-review hashes also match their quoted identities. Historical receipts are corroboration, not substitutes for current code analysis.

## Findings

**BLOCKING R155-OWNER-1 — common-session ownership is removed.** Location: sole input hunk, candidate_scheme.rs baseline 505–583, proposed target 505–535. The input replaces a session plus route index with independently supplied route, arena, effect state, registration table and occurrence. InferenceSession owns graph, batch and store together (lib.rs:7933 onward); the committed wrapper derives all of them from that owner. The replacement checks local registration and occurrence equality, then compares use/context fields which extraction itself copied from the same route (scheme:487–497). These comparisons do not authenticate the permission state's owner. The lower binder (effect:557–601) checks its own registration/permission fields but trusts caller-supplied mapped row and use.

Conditional falsifier: take authentic route/arena from session A and authentic permission/state/formals from session B collected from the same source, with matching registration, source occurrence and raw entry ordinals. Extraction operates exclusively in A; permission selection exclusively in B; no cross-owner identity is checked. Rust borrow lifetimes do not equate owners. This violates the contract's exact common-session witness and the retained-evidence ownership obligation in design-authority's proof-obligation-economy policy. Minimum closure: retain the current session-owned wrapper, or independently establish an unforgeable common owner across all supplied components under a new exact review. Equal numbers or source IDs are insufficient. This is an API/certificate countermodel under stated premises, not an executed source-program suppression bug.

**Major R155-ORIGIN-2 — deleted source and row joins have no substitute.** Locations: deleted scheme:522–575; surviving extractor:456–498 and lower binder effect:557–601. Removed checks select a unique context origin and Lambda recipe, validate source HIR Lambda/parameter, authenticate the raw negative Effect entry, compare current canonical captured-row representatives, and authenticate the mapped native negative Effect ordinal. Extraction checks Function/child structure and route maps, but does not perform these full joins. Lower permission lookup establishes local permission provenance only. Capture (scheme:3022–3055) and FreshUse (4608–4633) retain useful construction evidence, but the replacement no longer ties that evidence to the supplied permission owner. The contract requires exact permission/source/native correspondence; annotation-effect-hygiene integration §§1.1–1.2 requires permission, actual inflow and actual subtraction to remain distinct. Minimum closure: preserve these checks or provide exact constructor/transport arguments discharging each removed relation for every admitted caller. No reachable malformed same-session history is asserted by this finding.

## Hunk and semantic adjudication

The sole hunk contains no independently justified nonempty delta: the reviewed session-owned R152 repair is already present. The replacement comments and local equalities do not repair a new cause. HOLD of the complete residual and the exact NO_PATCH marker are appropriate.

Registration label, packed permission position, permission concrete-member index and native view/member coordinates remain distinct. Receiver:1870–1899 selects by registration while checking the carried packed slot/pointer and concrete member; receiver:5158–5196 independently selects the first matching concrete position. Example registration 7, packed slot 0, concrete vector [4,9,9] disproves their generic identification. Full selected operation identity is separately checked at receiver:1890 and 5149–5154; same-family ping and pong are not interchangeable operations. R155 adds no consumer and proves no suppression. No provider-equals-Lambda-constructor-owner restriction should be added; returned/local functions can have a supplying definition distinct from their source Lambda owner.

Committed call-site search finds this binder's definition only. The tuple FreshUse reconstruction test at scheme:6834 onward exercises structural copying, not cross-session permission authentication; it cannot certify this replacement. No test was run. There is no evidence here for runtime reachability, actual erroneous handling, successful inference, or theorem closure.

The implementation and proof handoffs correctly retain these qualifications, HOLD the input and propose NO_PATCH. No additional blocking finding against those dispositions.

## Scope and limits

Governing sources read: root AGENTS/base map, R155 contract, design-authority, top-level inference principles, and authoritative annotation-effect-hygiene integration §§1–1.2. Source analysis used only committed blobs and immutable submission artifacts. Live dirty scheme/receiver and quarantined runtime files were not read. No files edited, Git mutation, patch application, tests/build/Lean, scratch/cache/environment/worktree, or descendants. The 300-second review ceiling was not extended; precise CPU/RSS telemetry is UNKNOWN.

Original parent quantifiers, source domain, source/native bridge, INITIAL-STATE, CONSUMER, effect hygiene, soundness, principality, termination, original A/B and production remain OPEN. This review permits freezing the research HOLD/NO_PATCH result only.
