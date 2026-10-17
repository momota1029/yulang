# c2 typed native call — independent exact-conformance review

Revision: 1
Reviewer: `/root/c2_typed_call_spec_review`; no descendants.
Observed model/effort: UNKNOWN / UNKNOWN.
Launch: assignment receipt; exact launch clock was not captured. First observed clock: 2026-10-17 04:17:32 UTC.
STOP: 2026-10-17 04:18:17 UTC. Approximately 60 seconds allocation elapsed; exact total UNKNOWN because initial clock was not captured. No continuation or budget expansion.
Sole output lease: this receipt. Static read-only review of all other paths.

**Verdict: CLEAN for the bounded correction and conditional source/native derivation. Parent result remains PARTIAL.** No BLOCKING, major or minor exact-conformance discrepancy found. This review does not adopt semantics or authorize implementation.

## Authority and scope

Read `rules/design-authority.md`, `notes/design/INDEX.md`, root operating instructions, `rules/testing.md` (including Expected-output protection), top-level inference principles §§1.1/4, inferred Function call views §§1–2/5, original joint FORWARD-FIRST-CALL §§1–2, the contract rev3, source correction/handoff, proof/handoff, prior phase/carrier analysis and prior compiler receipt. Current target paths have no unstaged diff against HEAD; review concerns their exact frozen bytes and the explicitly withdrawn predecessor claim, not an inferred unstaged patch.

- Source correction §§1–2 and proof §§1–3 conform to contract Outcome/Source correction: `callee2+ <= N2-` is the initial whole-call relation; `arg(N2)` is the actual Positive argument endpoint. `candidate_source.rs:980–1050`, `shadow_apply.rs:1560–1674`, and `candidate_call.rs:437–532` independently establish child/owner/cause registration and retained native polarity. The constructor establishes slot 0; the observer alone does not authenticate arbitrary forged records as slot 0. Auxiliary effect slots 1/2 remain separate (`shadow_apply.rs:1680–1743`).
- Source correction §2 explicitly withdraws rev1 C-AppArg and its positive-to-positive admission formula. Conditional `arg(N2)+ <= arg(P)-` requires an actual PositiveFunction P compared with N2 and ordinary decomposition. `lib.rs:12550–12554`, `12644–12674`, `14179–14220` confirm all four child polarities. Neither a positive row nor an allocation establishes that premise or successful discharge.
- Proof §1 explicitly retains construction-success premises and disclaims source execution/reachability. The scoped local-name rejection at `candidate_source.rs:1002–1004` prevents using this static lemma as proof that this precise c2 source reaches a successful registered constructor. This is an explicit bound, not an established compiler defect or source restriction.
- Source correction §§3–4 and proof §§4–5 preserve original quantifiers, carriers, providers, worlds, responses/raw resumptions/futures and correlated witnesses from original FORWARD-FIRST-CALL §§1–2. Graph/Bind retention and identity substitution apply to the same suffix and already well-formed telescope/already typed witness. They do not establish IF(g), semantic insertion, F2 admission, complete B_in, VIEW, CHECK, F1/FK1, model existence, reverse B or aggregate A/B.
- Function-call views §2 forbids Q/shape/comparison success from forming admission. The corrected artifacts obey it. Missing source-admission and complete-carrier rules remain underspecified/open at proof §5's owners. They are not repaired or adopted by this review. The correction is a claim/source-correspondence repair, not an approved spec change. Production, code authorization and semantic adoption remain absent under the contract Review/implementation boundary and design-authority Approval gate.

## Test contracts and expectations

Read existing identity/directional assertions at `shadow_apply.rs:1870–1925` and `2559–2617`. They retain source/formal row and distinct Demand/effect identities; they do not prove full admission or exact-source reachability. No expected output, fixture, snapshot, diagnostic or semantic test-name change is proposed or authorized. Any future change requires causal authority determination and pre-write review under `rules/testing.md#expected-output-protection`; a conflict with an approved contract requires explicit user approval under `rules/design-authority.md#approval-and-implementation-gate`.

## Independently verified bytes

All twelve listed dependencies were independently SHA-256 hashed. Ten unchanged pins match exactly. The source artifact and handoff use explicit revision-2 replacement hashes, preserving historical predecessor pins; no same-revision substitution is claimed. The historical source artifact from baseline `8f012935e` independently hashes to the recorded predecessor `e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9`.

- Contract rev3: `aaaff21bda20de6288fd660356e6fcb63460e76bae2d239b662746664cf11adf`
- Source correction: `a78c3b32db064e3e6add46daeb7395703fe453fb6aba74ba9d98ce82ed409d25`
- Source handoff: `3bc79093b819f2de7029b81136bbfed0a3b9ef727acf68cb5c87696b184e9be4`
- Proof: `725c14759f92b85203b5d22894b0de1da95732448b50f0718a8879ed56243aed`
- Proof handoff: `923f792a915d8e3a95adf4d563f43c59f5cc99ff5ddf60d9ec07e6f1a7110b64`
- Prior compiler receipt: `dc944d612e45b687161292133c2838a42fc7f47fe923ebb8561e0bee3786900a`

Proof §6 records its actual historical contract rev2 pin, not a false rev3 provenance claim. Dependency hashes in proof §6 independently match the current exact sources; versioned predecessor/replacement accounting is explicit.

No tests, builds, probes, compiler/runtime execution, semantic edits, Git mutations or descendants. No fix required for this bounded packet. Original semantic owners and gates remain OPEN. STOPPED; writes stopped after this receipt.
