# R155 scheme residual source correspondence — revision 1

Assignment: `effect-permission-scheme-residual-r155-proof`, revision 1. Author and actual worker: `/root/r155_proof`; no coauthors or descendants. Sole output lease: this file. Sprint contract SHA-256 `1fb5c38fb14f6f11c1ac8d26930168f2b7bf0422948e4f79c0fcd3b916bd1309`; baseline `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`. The direct assignment and interim active-work messages establish execution. Requested model/effort and observed model/effort: **UNKNOWN/UNKNOWN**; no model is inferred from the role name.

Outcome: **source-native-evidence / conditional API falsifier; HOLD the complete residual**. It removes the session-owned boundary already repaired by R152 and reviewed for exact source-only integration in R153. No safe nonempty source change is justified by this proof lane. No source edit, candidate application, execution, theorem closure or production authority follows.

## Parent and application

The original parent remains the R154-recorded `YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128`):

`∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.

This packet does not inspect or execute that Lean declaration; its locator/type are reused from the authenticated R154 handoff. Original quantifiers, accepted language, lexical scope and ONE shared witness remain unchanged. The local question is whether one successful module permission binding joins the actual retained source permission, source Lambda, capture and FreshUse from the SAME inference session. The proposed interface cannot establish that fact from its independently supplied arguments. This directly blocks using its return as the same-session witness in the parent correspondence. INITIAL-STATE, CONSUMER, effect hygiene, native correspondence, original A/B, principality, termination and production remain OPEN. F1/FK1 and foreign continuations receive no discharge here.

Annotation hygiene §§1.1–1.2 retains permission, actual inflow and subtraction result separately. A `[signal]` permission permits the actual Catch to handle signal while additional write remains outward; permission alone neither supplies inflow nor performs suppression. No provider-equals-constructor-owner restriction is introduced for returned/local functions.

## Authentication and frozen evidence

All Rust reads below used read-only `git show` at the named baseline, never the live dirty files. The one residual hunk was reconstructed entirely in memory, checking every context/deleted line exactly, without offset/fuzz and without filesystem patch application. Its reconstructed target matches the contract.

| Input | Actual SHA-256 |
| --- | --- |
| R155 immutable input patch | `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f` |
| baseline `candidate_scheme.rs` | `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2` |
| reconstructed target scheme | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| baseline `candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| baseline `candidate_receiver.rs` | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| baseline `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| baseline `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| baseline `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| baseline `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| additional committed `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| R152 proof handoff | `ac040d9ad233fce3ac29b9e5fe3b092261d30a7003bf41238f96e151fe9c0b39` |
| R152 source handoff | `a18dc477d33e639b002cd22d4825e56640c7ab6c25b0a1f4eebc61974c58094c` |
| R152 independent review | `06d4aef333b67986454ce234a7a57c335549394c5b5fb90ab6a1e6f150ac2914` |
| R152 outcome | `0ef2328f1a629ef7dfaac16fb9d01525c10fbab56f9f83eadca8ea123b1cbf96` |
| R153 exact integration review | `30b9e143ad6e51e84e60f9c955d334d526bea07b3bc8f00334400f1b624fa1c7` |
| R154 proof handoff | `6f8cb681b7e4c19a1d9f4a299f6c50d3aace2e9fa5c7d2ac5f467998366d4279` |
| R154 source handoff | `3e43755b3b970c780739727bea80e7d0179a2bd11a02f42cebe3543f262b5d66` |
| R154 independent review | `dce151fb043b73114079a15185f464a0266acb3206ef60e8d205807a5fd644eb` |
| R154 outcome | `575281653810badf97dc4da8d20aee761893182b70273a6890a6bc80c3c3e3d5` |

Short Rust names are under `crates/yu-solver/src/`; prior handoffs/reviews have the exact `effect-permission-session-isolation-r152`, `effect-permission-session-isolation-20261102-r152/r153`, and `effect-permission-receiver-ownership-r154` / `effect-permission-receiver-ownership-20261102-r154` locators used by the contract. Their authors remain the authors recorded in those immutable receipts; this file only authors the R155 audit. Governing sources read: root AGENTS/base map, goal-driven sprint rules, assignment protocol, proof skill, design-authority rule, annotation-effect-hygiene integration and top-level inference principles.

## One source witness through capture and FreshUse

1. `InferenceSession` owns its `candidate_graph`, `batch` and `store` (`lib.rs:7933–7943`). `ConstraintBatch` is Clone and retains source artifacts through Arc fields (`866–872`). Equal source identity is therefore compatible with distinct sessions; local vector/row/use ordinals do not identify a session.
2. `candidate_formal_entry_annotation` (`candidate_effect.rs:1991–2050`) obtains the registration from **self.batch**, validates computation role, annotation owner, scope, parameter recipe, source-owner map and the exact HIR Lambda/parameter, rejects an existing permission for that registration, copies the original ordered concrete vector, and publishes it into **self.candidate_graph**. Only nonempty concrete rows produce records. `FormalEntryPermission` retains registration, actual source owner, Lambda occurrence, formal, scope, annotation/source-row positions and raw entry (`435–445`). This is permission provenance, not provider or Catch authority.
3. `retain_lambda_argument_effect` (`candidate_context.rs:1644–1651`) retains registration, Lambda occurrence, actual constructed Function term and raw Effect entry. Capture selects that exact positive Function endpoint, follows child 1 and checks its captured row against this session's canonical representative of the raw entry (`candidate_scheme.rs:3022–3055`). The raw entry is copied separately into the capture; equality of canonical representatives never chooses the registration or source Lambda.
4. `prepare_candidate_fresh_use` obtains a context-use identity from **self** context (`4523–4526`); `begin_use` increments that context's local counter (`candidate_context.rs:3539–3541`). FreshUse verifies the same Function/child/graph-row relation, maps it through the ONE shared row vector and copies registration, Lambda and raw entry unchanged (`scheme:4608–4633`). Publication moves graph, mapped rows and retained maps into the same session's route (`5045–5054`). Route `source_owner` is the receiving owner; `provider` names the target definition supplying the value. Neither is defined to equal the original Lambda's constructor owner.
5. Native extraction (`scheme:456–498`) authenticates positive Function shape, child 1, graph-row position, retained mapped Effect row, native Function term and its actual argument-effect child in the supplied arena. This proves a structural relation for that **route/arena pair**. It neither checks raw argument-effect ordinal nor authenticates the independently supplied permission state's session.
6. The committed wrapper (`505–583`) derives all arguments from ONE session, reselects the unique registration-labeled context origin, compares its exact Lambda and raw entry, checks the original native negative Effect variable, unique Lambda recipe, HIR Lambda/parameter, current canonical captured association, and mapped native negative Effect ordinal. The lower State binder (`effect:557–601`) uniquely selects a permission by registration and compares formal, owner, scope, occurrence, raw entry and nonempty payload. It borrows the exact concrete slice. These two layers jointly provide the retained same-session association; the lower layer alone accepts a caller-supplied mapped row/use.

## Exact residual disposition

The input has ONE hunk, replacing the wrapper and its comments. Capture, FreshUse, raw-entry retention and the lower permission binder are already integrated in the baseline and receive no new change here. The residual replaces `(session, route_index, incidence_index)` with independently supplied route, store, effect state, formal slice, registration and occurrence. It deletes the six provenance groups described in step 6. Its surviving registration/Lambda equality and route-use comparisons do not establish a common session owner or replace those checks.

The returned native incidence obtains `definition_use` and `context_use` directly from that same route; comparing them back to the route is not independent authentication of the permission state. A shared Rust lifetime only constrains borrowing duration. It cannot equate the allocations or owner sessions of separately supplied values. R154's constructor-based redundancy argument concerns a different private projection that starts from one owner and retains same-record pointer joins; that argument does not justify this exposed scheme wrapper with independent arguments.

The old provider-equals-constructor-owner predicate remains absent from both baseline and target. Its removal is already integrated, supported by the R152/R153 source-Lambda witness, and supplies no new safe slice in this residual. Restoring it would conflate the supplying definition with the actual source Lambda owner.

## Conditional cross-session falsifier

Let distinct sessions A and B start from cloned copies of one collected batch and reach the same authentic annotated computation Lambda and module-route incidence. Assume equal registration `r`, raw entry `e` and shared source occurrence, with authentic route/arena extraction in A and an authentic retained permission/registration in B. Call the proposed wrapper with A's route and native arena, B's effect state and registration slice, and those shared source coordinates.

Native extraction and both route-use comparisons run entirely on A. The lower binder selects B's permission by `r` and checks B's registration against the same source occurrence and equal `e`; it accepts A's mapped row and use reference without checking common ownership. Under these premises the result joins B's retained concrete permission with A's route/FreshUse. No foreign Term is looked up in B's arena, so arena rejection of foreign Terms cannot repair this join. Source IDs, equal numbers and a common borrow lifetime do not prevent it. Independent `begin_use` counters can also coincide; the lower binder does not consult B's use inventory at all.

This is an explicit conditional API falsifier, not an executed source program or established suppression bug. Paired reachability with the required successful source shape/equal ordinals has not been run. The committed single-session wrapper prevents this particular argument composition by construction. `R155-OWNER-1`: retain that wrapper or supply a separately reviewed unforgeable common owner checked across all independently supplied components; additional numeric/source equality is insufficient.

## Distinct coordinates and operation identity

Formal registration `r` indexes all `candidate_call::State.formals` (`candidate_call.rs:10–29`). Packed permission slot `p` enumerates only retained nonempty concrete rows (`effect:548–551,2015–2050`). Permission member `m` indexes that record's ordered concrete vector; native view/member `(v,n)` selects an operation-view family. These are distinct from raw row `e`, captured graph-row index, its current representative, and mapped FreshUse row. The scheme binder selects by registration and transports rows; it does not establish `r=p`, choose `m`, or authenticate an operation/arm.

Concrete interface falsifier: registration 7 retained at packed slot 0 with concrete vector `[4,9,9]`; selected family 9 has first member 1 while native member may be 0. `permissions.get(7)` misses and a read at member 2 still returns 9 without proving first-position provenance. These finite coordinates refute a generic coordinate equation, not a newly source-qualified two-definition execution.

The committed receiver preserves the separate actual receipt: unique registration selection plus carried packed slot/permission pointer, `.position(provider_family)`, carried member and indexed read (`receiver:1870–1899,5158–5196`). It also compares full provider/selected-operation identities (`1890,5149–5154`). Same-family `signal::ping` and `signal::pong` need not be the same operation. R154 independently held deletion of that observer evidence; the actual residual decision separately uses `source_operation_match`. This R155 residual neither adds an actual consumer nor changes that decision. Loss of the scheme ownership witness cannot be reported as demonstrated erroneous suppression, and a borrowed permission record cannot certify handler execution.

## Remaining evidence, resources and STOP

Reused R152's same-session source argument, R153's exact baseline target identity and narrow source-only authority, and R154's coordinate/operation/member distinctions with all original qualifications. Rejected transferring R154's private-constructor redundancy to unrelated independently supplied arguments. No historical conditional proof, unexecuted test or source review is promoted to a checked whole-language theorem.

`R155-ORIGIN-2`, owner scheme binder/capture through Luna: preserve the unique origin/recipe, actual raw native Effect row, source Lambda/parameter, canonical capture and mapped native row relations unless a later exact constructor proof discharges each removed check. Falsifier: a successful binding whose retained Lambda/raw entry/captured representative/mapped native argument-effect disagrees. This packet supplies the exact missing checks and owners, not evidence of such a reachable mismatch.

`R155-BRIDGE-3`, owner source/native proof lane through Luna: supply authentic initial Action/Inputs and SAME permission/capture/FreshUse interpretation before applying the parent judgment; retain independent provider/selected-operation and ordered member evidence at the actual consumer. The first missing source evidence is common-session authentication for the proposed API, followed by removed origin/row checks. No Lean term, theorem audit or source-to-Lean decoding was executed. A future fixture or code patch requires primary authorization and its exact gate; these TODOs grant no source leases.

Checks: SHA-256 authentication; committed source inspection; static exact one-hunk in-memory reconstruction; constructor/reader branch analysis. No tests, Cargo/build, Lean/Lake/checker, source writes, patch application, Git mutation, scratch/cache/environment/worktree/checkout, external contact or descendants. Several combined displays were truncated; decisive wrapper, lower binder, capture/FreshUse and receiver regions were reread in bounded selections. Budget ceiling 600 seconds; precise elapsed/CPU/RSS uninstrumented and UNKNOWN, no extension claimed.

All new paths: this sole leased Markdown handoff. No scratch/generated paths. Next step is Luna intake and fresh independent review against the implementation lane's frozen disposition; this author cannot certify the combined result. Revision 1 is FROZEN after hashing; the actual-byte hash is returned separately. **Writes STOPPED after this submission; no descendants or pending processes.**
