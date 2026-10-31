# R118 proof handoff — revision 1, CONSTRUCTED / UNCHECKED

Sprint `EFFECT-PERMISSION-DECODER-TO-LEAN/20261102-R118`; contract revision 1 SHA-256 `e86fa497f512dceefde4cdc98c1eda28c37d2978a9017626e43f1ca141d29d7a`. Assignment `/root/r118_proof`; exact leases are this handoff and `notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean`. No descendants. Requested/effective model, effort, CPU, RSS and runtime telemetry: UNKNOWN; no model execution receipt was exposed. Live assignment and primary clarification authorize only this bounded leaf and exact read-only pinned Git blob reads.

Outcome: **conditional finite candidate plus source-grounded obstruction**, not an operational Rust-to-Lean bridge. The six candidate theorems are UNCHECKED. No printed types, actual Lean goals, diagnostics, kernel acceptance or axiom lists were obtained. Embedded audit commands are future commands only. No independent-review or production authority is claimed.

## Sources and unchanged parent

Semantic authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`. Permission, actual inflow and residual remain distinct. Contravariant `[signal]` grants local subtraction; `[signal, write]` input remains admitted and write stays outward. Concrete identity retains resolved arguments. The 2026-10-11 inference principles preserve ordinary Simple-sub generation/propagation and require constructor evidence at its owner.

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean` lines 128–130, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

`∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.

The original lexical scope and ONE shared witness remain fixed. `docs/yulang-whole-proof-closure-ja.md` §§1,3–4, SHA-256 `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`, preserves all accepted source constructors and its opening birth-level SCC correction. Neither the draft closure manuscript nor this candidate supplies semantic approval. No source form has been excluded from the parent.

Local parent theorem types, in namespace `YulangClosure.SuppressionPermissionR116`:

- `selected_endpoint_member`: arbitrary complete identity type `Id`, decidable equality, R39 `e,a,f,r,port,p`, provider/arm and decoded endpoint family; hypotheses `prepare e a = some (f,r,port)`, `permissionFor a f r port = some p`, `SelectedSource a r arm`, `operationMatch provider arm = true`, `endpoint = provider.family`; conclusion `endpoint ∈ p.concrete`.
- `internal_certificate_member`: arbitrary artifact/identity/term/fact types with decidable equalities; SAME `e.source`, action/row and `probe.permission`; hypotheses the two R39 equations above, R45 `extract e q probe = some out`, same selected row and operation match; conclusion exact output registration, occurrence, formal owner and provider-family membership in `out.permission.concrete`.

Neither parent theorem was applied with invented inputs. Their existing `#check` and axiom lines were read, not executed.

## Frozen inputs

The following SHA-256 pins were independently recomputed by `sha256sum`, exit 0:

| Input | SHA-256 |
| --- | --- |
| R39 `ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R45 `InternalPermissionIncidenceR45.lean` | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| R54 `OwnedResidualProjectionR54.lean` | `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9` |
| R116 `SuppressionPermissionR116.lean` | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |
| R117 patch revision 2 | `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` |
| R117 Rust handoff revision 2 | `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e` |
| R117 independent review 2 | `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664` |

Read R118 admission and R117 closeout before construction. Rust source was read only at `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, exact paths `crates/yu-solver/src/{candidate_receiver.rs,candidate_effect.rs,candidate_source.rs,lib.rs}`. Their contract blob pins are respectively `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`, `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`, `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`, `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`. These four blob hashes are inherited pins; this worker did not independently recompute them. No dirty Rust source was read or patch applied.

## Construction, exact declarations and premises

Artifact SHA-256: `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`.

All six theorem names below have prefix `YulangClosure.NativePermissionDecoderR118.`. Their stated types are source declarations, NOT printed Lean receipts.

1. `contains_member`: arbitrary `Id` with decidable equality, list `xs`, family; recursive equality-based `contains xs family = true` implies `family ∈ xs`. Proof recurses over the actual list and equality branch; membership is not a hypothesis.
2. `read_family_exact`: `readFamily views endpoint = some family` implies an actual list `allowed` with `views[endpoint.view]? = some (endpoint.view, allowed)` AND `allowed[endpoint.member]? = some family`. The native coordinate remains a pair of natural indices; no index is cast to an `Id`.
3. `read_permission_exact`: `readPermission permissions registration storage = some p` implies `matching permissions registration = [(storage,p)]`. `matching` executes a registration-field filter. Exactly one retained entry and its separately checked storage coordinate are derived by case analysis, not assumed as membership.
4. `decode_member`: arbitrary owner state/batch types with decidable equality, two full R54 owners, concrete view/permission inventories, endpoint, formal registration, packed storage index, family, permission. Its ONLY substantive premise is the explicitly defined partial `decode ... = some (family,permission)`. It concludes full state/batch owner equality, the two actual view/member read equations above, exact singleton filtered retained permission at the distinct storage coordinate, and `family ∈ permission.concrete`. It inverts executable owner/read/any branches and invokes list induction. This `decode` is a PARTIAL guard transcription, not a FaithfulDecoder assumption or the full successful Rust predicate.
5. `unequal_coordinates`: finite candidate where registration 1 selects retained slot 0, native endpoint `(0,1)` reads family 7 and yields that exact selected permission. It explicitly states `1 ≠ 0` and `1 ≠ 7`; neither storage nor member is identified with registration/family. Proof term is `by decide`, UNCHECKED, not an executed test.
6. `post_state_is_not_prepare_input`: the existing R45 finite witness permission passes these local view/permission/any guards, while R39 `prepare` on `postInputs` returns none because retained registration 0 is already present. Again `by decide` is constructed text, not kernel computation observed in this packet.

No theorem takes permission membership, `prepare`, `permissionFor`, `SelectedSource`, operation identity/match, R45 `extract`, `LocalLaws` or a catch-all faithful interpretation as a hypothesis. No theorem claims to establish those missing obligations. Lists retain duplicates and order. R39/R45/R54 are reused as imported model definitions, not asserted as concrete Rust instances.

## Source path and exact remaining obstruction

Actual pinned source sequence inspected:

- `candidate_source.rs:1322–1327`: SAME Lambda parameter annotation produces `Action::FormalEntry` with actual formal registration, occurrence and formal scope; executor at line 2463 invokes the constructor.
- `candidate_effect.rs:1762–1821`: constructor reads annotation effects, checks variable count, formal role/owner/scope/recipe, source owner and exact source Lambda; rejects already occupied formal domains/registrations; copies the whole concrete vector; publishes only after symbolic links succeed. This is the supplier of R39 constructor equations, not the later inventory read.
- `candidate_effect.rs:449–487`: Internal permission lookup selects uniquely by registration, checks all retained identity fields and nonempty concrete vector; returns `concrete: &permission.concrete` from that exact record.
- `lib.rs:18320–18460`: exact use, Internal receipt/fact, registration/recipe/root and Lambda origin; positive Function child and original negative entry; slot-2 Lambda fact; then SAME permission lookup.
- `candidate_receiver.rs:5052–5125` plus frozen R117 hunks: same borrowed inventory/state/batch/owner, `AnnotationMember`, exact view index/pointer, closed tail, exact allowed-member family and operation-origin checks; retained registration-keyed source join; `InventoryPackage::capture` carries reference/storage/member/family.
- `candidate_receiver.rs:1860` plus R117 consumer hunk: unique registration lookup, separate retained storage check and exact permission pointer; actual owner-view allowed read and concrete `.iter().any`. Those last finite reads/any are the portion represented by this module.

FIRST missing constructor/read: an authenticated interpretation of the actual `Action::FormalEntry` and its **pre-constructor** batch/effect state as R39 `Inputs`, `Action`, `Registration`, `Row` and port. In particular identify the original `registered.owner` LocalSource Lambda read and SAME `parameter.annotation.ty.effects` row, and show the two absence checks hold at the constructor event. R117 retains the resulting permission and observation owner, but does not materialize that temporal constructor event as Lean data/equations.

Concrete falsifier for the naive current-state substitution: after publishing registration 0, `retainedRegistrations = [0]`. Its exact permission remains present and the owner-view contains family 7, so the local decoder succeeds, but `prepare` on this POST-state is none. `post_state_is_not_prepare_input` records that finite case. This is an obstruction to identifying a post-state projection with the R39 pre-state, not a counterexample to Rust behavior, R116 or original soundness. Recovering an actual earlier state/event is needed; inventing an empty retained list would lack correspondence.

Other separate unproved reads: Rust pointer and slice identity to shared interpreted record/list; `usize/u32` checked-conversion and bounds semantics; exact source row identity/singleton to `SelectedSource`; complete resolved operation/declaration interpretation to R116 `Operation` and `operationMatch`; every R45 owner inventory, unique receipt/plan/construction, original route/slot-2 fact, recipe/component, positive Function and negative entry read; actual state and batch pointers to the full R54 owner. The partial model does not pretend to derive any of these.

## Parent application, omissions and handoff

Conditional application now available: **IF** actual Rust reads are interpreted as the supplied finite owner/view/permission inventories and exact successful guards reduce to this partial `decode`, `decode_member` gives the decoded family membership in that SAME selected retained value. It reaches the membership conclusion of R116 `selected_endpoint_member` by a direct read/any route; it does not instantiate that theorem's constructor, selected-row or operation premises. The raw endpoint is NOT the `endpoint : Id` of R116; only its decoded family can fill that argument after the operation-family equation is established.

`internal_certificate_member` remains unapplied: its SAME `probe.permission`, R39 pre-state/retention equations and R45 `extract` must still be constructed from actual owner reads. There is no certified `out` here. Parent `InferenceSoundness` still lacks the original source derivation/shared scoped witness; this local lemma constructs neither. Effect hygiene, principality, termination, R114 admission transport, native correspondence and production remain OPEN.

Represented: finite closed owner-view member lookup, registration-keyed singleton retained selection, packed storage check, equality-based any guard, complete modeled state+batch equality, duplicates/order and unequal indices. Omitted from this partial model: Rust reference identity/provenance, full operation identity guards, original constructor/pre-state, entire R45 extractor, actual Suppress decision, propagation, symbolic variable links, arbitrary source annotations/arms, callback/nested result forms, provider arrival, FreshUse, continuation/replay and all whole-language cases. These remain accepted parent scope, not removed source forms.

Mutual TODO `R118-PRE-CONSTRUCTOR-READ-1`: primary source/native bridge owner must supply exact constructor event/pre-state, owning LocalSource Lambda and SAME annotation row, with read equations and stable permission correspondence. Falsifier: an alleged bridge uses post-state absence checks or exchanges an equal-looking annotation/foreign registration. No new source edit or resource lease is requested by this TODO.

## Actual execution and stop receipt

Read-only commands actually run: `cat`, `sed`, `rg` (one bounded result piped to `head`), exact-path `git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:<one of four pinned paths>`, and `sha256sum`. Tool-reported shell exits were 0 for these reads and the two exact leased-file heredoc writes. No material failed checker evidence exists because execution was prohibited, not attempted.

Project metadata read: `leanprover/lean4:v4.35.0`; `YulangClosure` 0.1.0; `-j1`, `-M1024`; empty external package list. Installed version commands, Lean/Lake/checker/compiler/Cargo/build/test/formatter, patch application, toolchain lookup/install and environment/resource probes: NOT RUN. All six printed theorem types and all six complete `#print axioms` results: NOT RUN / UNKNOWN. R108 aggregate output-cap and R111 Rust-cap boundaries were preserved with no retry. Future verification belongs to a newly authorized owner after those gates are resolved.

Finite budget ≤480 seconds; wall/CPU/RSS spent and remaining telemetry UNKNOWN. No scratch/temp/cache/generated/worktree paths were created or written. Only the exact two leased paths changed; no compiler, root import, shared status, rules, dependencies, questions or other worker files were edited. No Git mutation, descendants, scheduling or reviewer appointment occurred. **All writes STOPPED at revision 1 freeze; no generated outputs or descendant leases.** Pending fresh independent review and primary adjudication. Handoff hash is reported externally to avoid a self-hash cycle.
