# NATIVE-FRESH-USE-VALIDATION/r2 independent review

Assignment: `/root/native_fresh_use_validation_review_r2`; fresh source-first review, revision 1. Requested role in current state: `spec_auditor`; requested model/effort UNKNOWN/UNKNOWN. Observed effective role/model/effort unavailable from runtime metadata: UNKNOWN/UNKNOWN/UNKNOWN. Exact write lease: this report only. No descendants. State at ACK: ACTIVE; final state: **STOPPED / writes stopped**. Elapsed wall time, CPU and RSS were not measured and remain UNKNOWN; no estimated remainder is claimed. Reviewer grant: 600 seconds. No executable checks, builds, Cargo, Lean, Lake, Git or children were used.

## Verdict

**Do not accept the asserted Context obstruction as establishing `NO_SAFE_CODE_SLICE` for complete validation.** The full validator and proof are NOT_DELIVERED, and no closure follows. A viable safe readback/coverage slice exists through already pinned interfaces, including a post-bound route at the requested returned-root site. This review does not establish that every remaining validator obligation is implementable within the present lease or budget.

The Rust owner is byte-identical to the admitted baseline. The Lean output contains only a comment. They introduce no validator success path or theorem, so there is no new compiler correctness regression to classify. The material findings concern the submitted evidence and resulting owner/implementation decision.

## Method and authenticated inputs

Authenticated the contract and every contract-pinned dependency before reading source bodies. Inspected `candidate_context.rs` and `candidate_source.rs` before `candidate_scheme.rs` or producer handoffs. The initial decision used native constructors/readback, not producer explanations. Subsequently authenticated and read both handoffs and the comment-only Lean output. Read governing inference principles, the fixed contract, parent `Contracts.lean` scope, and existing scope/hygiene module limitations. Relevant tests were read in the pinned scheme owner; no test was executed. No unpinned native source owner was inspected.

All hashes below were independently recomputed and matched. Rust/workspace paths are relative to `isolated/native-fresh-use-validation-r2/`; Lean paths are relative to `notes/theory/lean/`.

| Input | SHA-256 |
| --- | --- |
| Contract `tasks/agent-loop/sprints/native-fresh-use-validation-20261028-r2.md` | `9764890e7d430cefa9765ead51d5496b7078cf077c0937f5555617b3f685a0f2` |
| `crates/yu-solver/src/candidate_scheme.rs` | `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e` |
| `crates/yu-solver/src/candidate_effect.rs` | `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6` |
| `crates/yu-solver/src/shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `Cargo.toml` | `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `crates/yu-solver/Cargo.toml` | `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed` |
| `YulangClosure/NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `README.md` | `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3` |
| `YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure/OriginalEffectHygiene.lean` | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| Frozen Rust handoff `tasks/agent-loop/inbox/native-fresh-use-validation-r2-rust.md` | `4bb6f45a2bea9ea5fd0f46bcb416800edce1d34e2cf6f897ded96f560852a093` |
| Frozen Lean output `YulangClosure/NativeFreshUseValidationR2.lean` | `1cacf6a449ca8fb2a7baf6bb4187073738842e07dd2129a0e37472b7c31c281c` |
| Frozen proof handoff `tasks/agent-loop/inbox/native-fresh-use-validation-r2-proof.md` | `2e2b3473f0e85d03626d3ec6d89a205abbda011137474abab6ff009668ff29f1` |

## Findings

### major R2-REVIEW-1 — the first claimed inaccessible field has an existing authentic readback route

Locations: Rust handoff line 9 and proposed escalation at lines 14–15; Lean output lines 7–15; proof handoff section “Constructor evidence and first inaccessible field”, final bullet. Owning source: `candidate_context.rs:1054`, `1090`, `1094`, `1167`, `1184`, `1191`, `1220`; caller/consumer: `candidate_scheme.rs:4266`, `4267`, `4431`, `4448`, `4697`; native transport: `candidate_context.rs:4287`.

Concrete issue: the Rust report says no readback accessor exists. `CircuitEvidence.contexts()` and `.weights()` borrow actual immutable State entries. `State.retained_input` is callable from this module and supplies that evidence. Its `Incomplete` status does not mean its borrowed context constructors are unobservable: `FilterObligationsUnavailable`, `ProducerReadinessUnavailable` and `DependentObservationsUnavailable` are pushed unconditionally at lines 1312–1314 for the broader certificate obligation. Treating that status as missing readback conflates two phase responsibilities.

Alternate path at the required core return, independent of candidate-map mutations:

1. Derive roots from **all** `graph.bounds` relations, exactly as `prepare_candidate_fresh_use:4419` does. Capture source constructor evidence before remapping, rather than choosing roots from the map under validation. `retained_input` selects each relation's raw context and its complete child closure. `relation_context` uses the post-check context; in the current owner, a successful discharge residual is the original root, a `PrefixLeft.input` descendant, or identity (`candidate_context.rs:3678`, `3708`, `3750`, `3878`, `3297`). Thus it does not create an inaccessible detached source constructor.
2. `rename_contexts_impl:1583–1670` visits precisely the reachable source DAG, inserts identity when reached, checks all children precede parents, and interns each renamed node with the mapped ordered children and weights. Repeated roots/sharing do not enlarge the required domain.
3. Before `freshen_candidate_graph_core:4277` returns, the loop at 4267–4270 has admitted every bound. For every bound with a relation, `begin_candidate_fresh_bound:4697–4706` uses the corresponding mapped root as the new relation context. `candidate_context_fresh_transport_scoped:4287–4288` retains that exact context and an explicit parent/child Transport dependency.
4. A post-bound `retained_input` from the original Graph relation roots expands both ends of each touching dependency, repeatedly to closure, then selects every context child and weight (`1184–1251`). Therefore every successfully emitted mapped root and child is observable at this phase. Zero bounds/zero relation roots yield an empty rename domain; identity has the defined zero representation and no table entry. Missing, extra or replaced candidate map entries can be checked against source-derived domain plus unchanged borrowed target constructors, failing closed if any needed observation is absent.

This is a source trace, not a tested coverage theorem or acceptance of a complete validator. It suffices to defeat the submission's blanket interface-impossibility conclusion. A pre-bound detached `prepare_candidate_fresh_use` result at 4665 is a different phase: fresh target relations do not exist yet. The local route also retains this intermediate state at 5024–5031 and restores bounds before using its root at 5152–5168. That seam needs an explicit validation phase choice; it does not justify ignoring the post-bound core return that the packet names.

Violated contract: Fixed outcome's requirement to establish whether admitted interfaces support authentication, required evidence clause 5's **first missing native field** criterion, and repository cause/owner and proof-obligation-economy rules. The proposed new Context API is not yet shown necessary.

Minimum closure: revise the obstruction claim, and construct or refute this exact source-root/post-bound readback coverage route for every map entry, including discharged parents, shared DAGs, identity, no-relation bounds and local suspension. If a remaining source/target is inaccessible, supply a concrete successful native construction and precise ID/owner absent from this closure. Until then record **complete validator NOT_DELIVERED; readback coverage slice viable; full feasibility OPEN**, rather than certified `NO_SAFE_CODE_SLICE`.

### major R2-REVIEW-2 — additional claimed allocation/payload impossibility is not an owner-interface obstruction

Location: Rust handoff line 11, proposed owner expansion at line 14. Source: `candidate_effect.rs:307–308`, `333`, `360`, `1039–1081`, `1336–1359`, `1395–1417`; scheme-local construction at `candidate_scheme.rs:4386–4444` and retained fields at 593–608.

Concrete issue: absence of an allocation cutoff or temporary View map in the **existing** FreshUse record is presented as inability to authenticate under the leased interface. Both contribution/view vectors and their payload fields are readable from `candidate_scheme`; this is also correctly acknowledged by the proof handoff and Lean comment. Contribution IDs/instances come from the vector's pre-push length. The scheme owner can capture that length before its ordered contribution allocations and retain separate constructor evidence. View copies return actual IDs at scheme-owned call sites; a construction recorder can retain those outputs independently of the map later subjected to mutations. `validate_payload_view` additionally authenticates native weight/view linkage, and selected weight payload readback exists as above. These possibilities do not require modifying `candidate_context.rs` or `candidate_effect.rs`.

Risk: an unwarranted owner/API expansion substitutes new machinery for examining construction evidence at the already leased caller. A clone of an untrusted candidate map alone would still be invalid evidence; the missing work is an independently captured construction recipe, not proof that it cannot be built.

Violated contract: fixed conditional statement on actual fresh allocation/remapping outputs, required evidence clauses 1 and 5, and the prohibition on self-consistent supplied snapshots. No validator is delivered, so this is an evidence/adjudication failure, not a demonstrated unsound acceptance.

Minimum closure: either implement an allocation/copy recorder at the scheme-owned construction calls with unchanged native-vector readback and mutation falsifiers, or identify a concrete required field that those exact interfaces cannot observe. Preserve the proof lane's more accurate “accessible but not constructed” classification. Do not promote a proposed recorder into proven complete authentication.

## Remaining scope and evidence limits

The unchanged scheme still exposes seven Graph Node forms and 13 atoms; ordered children, sharing, polarities, dependent Record/Variant fields and term readback are visible in `term.rs:198` and the constructor traversal at `candidate_scheme.rs:4455–4575`. Existing tests at 6430, 6497 and 6562 inspect variant tags/arity, record presence, both polarities, shared row images and tuple child order. The retained-map test at 7365 checks lengths/capacity transfer. These are useful sibling contracts, not the required mutation falsifiers or proof of exact domains.

`candidate_source.rs:189–193`, `296–359` exposes scope maps and actual allocation/forest transformations. No new evidence here proves scope-domain/freshness, scoped relation/demand remapping, context-use freshness, bundle/evidence authentication, source-obligation indices or all seven-form root correspondence. Full context readback coverage and correct recipe interpretation still need construction and independent review. No unsupported success branch has been added.

Lean declarations delivered: none. Printed types/axiom audits/kernel checks: NOT_RUN. The two existing pinned scope modules explicitly leave native allocation/resource success, region ownership/origin payloads and full Context/Call/effect interpretation separate. `Contracts.lean:128` is the original quantified proposition definition; it is not a proof instance. `OriginalEffectHygiene.lean` explicitly leaves the complete source interpretation open. Parent soundness, principality, termination, source/native correspondence, effect hygiene and production gates remain OPEN; H_u remains AUTHORITY_BLOCKED.

No BLOCKING compiler finding or minor style finding is asserted. Both major evidence findings require primary adjudication before treating the submitted obstruction as an accepted outcome. No source, handoff, proof or shared status was edited; only this report was authored. Final state: **STOPPED; writes stopped; no unresolved descendant leases or persistent processes**.

## Concrete next packet recommendation

An r3 packet should target **only the existing-API Context readback/coverage slice first**, under the same research-only boundary: derive source relation roots from Graph bounds; capture source closure and the actual `relation_context` roots before rename; enumerate authentic post-bound target closure through `retained_input`; establish exact expected context-map key domain and source/target constructor/child/weight readback coverage; reject or return an explicitly partial result for every absent observation. Preserve the r2 producers' frozen bytes. A safe collection/coverage result must not be called complete FreshUse validation and must not certify payload transformation, allocation identity or returned-root correctness merely from coverage.

This bounded packet can construct a source-owner coverage argument and its mutation falsifiers without a new Context API. It should explicitly cover module completion, local completion and suspended pre-bound states; pre-bound states may report partial/unavailable rather than falsely claim post-bound observations. If complete coverage fails, the deliverable is the exact successful source trace and missing constructor ID, which gives a justified narrow owner request. Full FreshUse validation remains unproved across every other retained map, native allocation, weights/payload transformations, all seven Node forms/13 atoms, shared root image and the Lean soundness/application obligations listed above. Further work should be selected from the resulting concrete remaining premise, not assume full feasibility from this review.
