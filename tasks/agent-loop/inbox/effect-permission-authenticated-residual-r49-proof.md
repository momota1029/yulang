# R50 constructive proof handoff — frozen revision 2

Assignment ID: `R49-LEAN-AUTHENTICATED-RESIDUAL` / revision **2**, correcting the R49 review under `EFFECT-PERMISSION-KNOWN-UNMATCHED-FORWARDING/20261031-R50`.
R50 contract SHA-256: `54a680db4806ca2387cb1a159c752f6495675225c76e017209a5a882e7ce33d2`.
Admission SHA-256: `b5bda4d96775235e8f0874e0a3c1d93db93c2ffd67994adef4c014d70c243792`.
Governing R49 review SHA-256: `cbb93d8a712222387b78b7278c39d089042ea8cb53ddc803c89621da0510307e`.
Primary-supplied admitted/pushed baseline: `590eaa937`, `yulang3`; no worker Git command was run.
Worker: `/root/r49_proof`; parent followup-task/resume receipt establishes this live R50 assignment. Requested/effective model, effort, authenticated active-time telemetry: UNKNOWN. No descendants.

Revision 1 is preserved byte for byte in the archive section below, hash `90bb99675de20fe8cf58c41fb14b7366f83eea2cd7487c0ba2fbf87419a85e71`. Its former module hash was `ba9800813d2b005ec023971ac88798e1b4e41f2a93b971ddc025d8985c844ce0`; its semantic compatibility claim is superseded by the blocking R49 review and this correction. Historical receipts are not current acceptance.

## Scope and repaired classification

Only the existing exact leases were written: `notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean` and this handoff. No compiler/test/expectation/config/toolchain/manifest/shared-status change; no Git, Lake/build/tests/Cargo, formatter, scratch, cache, target, environment, worktree, service or nested CLI. Frozen Rust revision-2 correspondence is **not claimed**: that separate lane was not frozen before this proof freeze, and the primary explicitly directed this boundary. This report is conditional mathematics/kernel acceptance, pending fresh independent review.

The governing sources and unchanged original parent scope are retained in revision 1. R50 additionally reads its exact contract/admission and the complete R49 blocking finding: a signal Catch with a write provider must forward the provider endpoint. Known mismatch cannot be inferred from missing identity, names, family membership or pointer inequality. The R50 contract corrects that private branch; it neither changes original A/B quantifiers nor shrinks the source language.

`Selection` now retains the selected operation's complete declaration key and family independently of the provider query. `SelectedArmReads` authenticates the actual original Catch/edge-scrutinee, first-arm ordinal, source/range, operation-pattern source, resolved selected declaration/family, empty-call syntax and wildcard continuation. `IdentityReads` separately checks the actual provider occurrence's retained `sourceOperation` read. `classifyIdentity` returns:

- `Classification.authenticatedMatch`: BOTH owner reads succeed, complete declaration identity agrees, and family data agrees.
- `Classification.knownUnmatched`: BOTH owner reads succeed and complete resolved declaration identities differ.
- `Classification.unavailable`: an identity/source read is missing or ambiguous, or the same declaration key has inconsistent family data.

Names and pointer comparisons are absent from classification. `Id` denotes a complete retained/branded declaration key, including allocation identity; establishing that interpretation from Rust remains an explicit extraction premise. `classification_known_unmatched_iff` exposes both owner reads and full-key inequality. `unknown_identity_unavailable` proves absent reads never become known mismatch and no endpoint gets a successful forwarding decision. Existing `providerCandidate` still rejects missing native view/member reads independently of identity classification.

`decideEndpoint` checks the source classification and native member read. KnownUnmatched forwards the ORIGINAL valid endpoint without attempting suppression authentication. AuthenticatedMatch can suppress only through the unchanged complete same-witness `Authenticated` checks; Unavailable returns `none`. Every suppression still implies `endpoint = target c ∧ authenticate c = true` by `suppression_iff`. `suppression_complete_authentication` recovers Match, all `Authenticated` checks, accepted SAME R45 certificate and R47 entry, same retained permission, common-terminal arrivals to both original rows and exact matching source arm. The expanded R49 `authenticated_prerequisites` and `accepted_suppression_applies` proofs remain checked.

The old failure lemmas `unavailable_no_publication` and `matching_gap_no_publication` now explicitly require `classifyIdentity c = authenticatedMatch`: their former assertion for a known source mismatch was the behavior being repaired, not a parent theorem to retain. `unmatched_decision` explicitly requires source identity availability. These corrected private statements are not relabeled as proofs of the former invalid branch. Full parent A/B, inference soundness/coverage and production are unchanged and OPEN.

## Constructive parent use and represented cases

`known_unmatched_plan` constructs a complete all-Forward plan from authenticated KnownUnmatched and successful native endpoint reads. It takes no accepted-plan premise. `known_unmatched_publish` derives the exact ordered `(original endpoint, upper)` trace; duplicates, the provider endpoint itself, and same-family siblings remain unchanged. The same `c`/original list/upper is used throughout. `fold_all_forward`, the unchanged `fold_correspondence`, and checked count-preservation lemmas keep identity and multiplicity explicit.

`concrete_known_unmatched_forwarding` constructs independent resolved signal-arm identity 40/family 41 and write-provider identity 31/family 7, with a checked R45 permission allowing the arm family 41. It proves IdentityReads, accepted R45 extraction, KnownUnmatched, a provider-origin native candidate, failed suppression authentication, a complete forwarding plan for `[7,8,7]`, and exact published pairs `[(7,9),(8,9),(7,9)]`. Thus the provider terminal is forwarded twice even though it is the exact target and suppression authentication is false.

`concrete_same_spelling_distinct_identities` assigns both distinct complete keys the spelling `ping` and still constructs KnownUnmatched forwarding. `concrete_r50_classification_boundaries` checks missing provider resolution, missing Catch/selected-arm source, authenticated matching identity with absent permission, matching identity with absent arrival inventory, and supported fully authenticated matching suppression. The prior positive logical Support/common-endpoint witness and same-family sibling witness remain checked. Other source pattern constructors remain represented in the syntax carrier; this private consumer's supported first-arm syntax is not a restriction on the original parent source domain.

Apply `known_unmatched_publish` to the nonmatching effect position of the original hygiene goal, with exact source reads and native endpoint inventory supplied by their owners. Apply `suppression_complete_authentication`/`accepted_suppression_applies` to the matching branch using the SAME R45/R47/R48 witnesses. First remaining premise/owner: Rust/source must extract these exact current source, operation, permission, physical and logical path inventories and show the concrete `constrain_live_effect` sequence implements this pure fold. Complete search/extraction, key/lifetime fidelity, source and Catch execution rules, native allocation/failure behavior, full subtraction/hygiene, original A/B, principality, termination and production remain OPEN. The primary owns source correspondence dispatch and fresh review. No source-qualified counterexample to the original full theorem is claimed.

## Actual checks and finite resource boundary

Final **Audit 11** checks all **35 explicit theorem roots**, prints every complete type via `#check @...`, and records every transitive `#print axioms`. Exit 0, no warnings/errors. Axiom sets are `propext` alone for `support_member_sound`, `lower_path_arrival`, `classification_match_iff`, `classification_known_unmatched_iff`, `fold_correspondence`, `fold_all_forward`; all remaining 29 roots use exactly `[propext, Quot.sound]`. No `Classical.choice`, `sorryAx`, project axiom or native-evaluation axiom occurs. Code-level source scanning of the entire concatenated local dependency cone found no sorry/admit/project axiom/unsafe/native_decide/checker bypass.

R50 Audit 10 also exited 0; its two unused-section-variable warnings were repaired using `omit`. Audit 11 is the only audit of the frozen revision-2 module. There was no failed Lean process or timeout in R50; earlier R49 failures remain preserved in revision 1. Full current per-root types, axiom outputs, inputs/dependency hashes and stdout/stderr hashes are in the R50 audit section below.

Same permitted route: cwd `notes/theory/lean`; command `taskset -c 0 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, each with Python subprocess timeout 120 seconds. Concatenation/audit-suffix construction is identical to the exact recipe in revision 1, using current R39/R45/R47/R48/R49 source bytes. No local `.olean` or generated output is used. The skill checker remains inapplicable under this packet because it builds/writes scratch; no helper or Lake invocation occurred.

Frozen revision-2 module SHA-256: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`.

Final Audit 11 input SHA-256: `d4ac170074404781684896c0e914347a9b75d5eddf5c5f208a81b777eb3c7442`; stdout SHA-256: `0b2057978b9b51658c4e574007ec8373daef71ddfc866fe0eb2c5a5138e52bb1`.

Observed installed version:

```json
{
  "argv": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "--version"
  ],
  "exit": 0,
  "stdout": "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)\n",
  "stderr": "",
  "stdout_sha256": "eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}
```

Measured R50 Lean subprocess resources: `{"r50_audit_processes": 2, "wall_seconds": 14.089589334995253, "user_seconds": 9.988113, "system_seconds": 1.126052, "peak_child_rss_kib": 877876, "per_process_timeout_seconds": 120, "cpu_affinity": 0, "lean_memory_limit_mib": 1024}`. Each process was bounded to one CPU. Grant <=900 seconds; no extension or extra resource request. Whole-agent active wall time/RSS and model/runtime telemetry were not independently instrumented and remain UNKNOWN. The finite packet ends here; these two kernel probes are not Rust runtime/model execution receipts.

Worker state: STOPPED. **WRITES STOPPED** after this numbered frozen handoff write. No descendants, scratch or generated-output leases. Fresh independent review and primary integration remain pending; source/native and parent gates remain OPEN. The handoff byte hash is reported outside this file.

## Byte-preserved revision 1 archive

# R49 constructive proof handoff — frozen revision 1

Assignment ID: `R49-LEAN-AUTHENTICATED-RESIDUAL` / revision 1.
Sprint: `EFFECT-PERMISSION-AUTHENTICATED-RESIDUAL/20261031-R49`.
Contract revision 1 SHA-256: `bbd29538d354355f1da604f6072544d3569887ff1fc9c0e449ec61c0afc67d9e`.
Admission SHA-256: `fe90989cbce2bbd86518eceb14920ecbffa221933399704473dbb94f2fd5bcce`.
Baseline: `yulang3`, `3b1ef27d3795b2bc56ab1718dcd3c06700699547` (supplied contract baseline; no Git mutation).
Worker: `/root/r49_proof`; actual parent task receipt and subsequent parent messages establish this assignment. Requested/effective model, effort, authenticated agent active-time telemetry: UNKNOWN. No descendants or external contact.
Outcome: **conditional mathematics, kernel accepted; independent review PENDING**. Source/native completeness, Rust syntax/type/runtime success, semantic subtraction, Catch execution, parent A/B and production remain OPEN.

## Exact outputs and scope

Only written paths:

- `notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean`
- `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-proof.md`

No scratch/generated/cache/`.olean`/target/environment/project-copy output was created. No Lake/build/tests/Cargo/formatter/Git operation was run. Existing generated outputs were not used or changed. Cache verification owner remains the primary; this lane used no cache. The skill helper was inspected but not run: `check_lean.py` lines 205–212 build modules and create an audit scratch file, both prohibited by this packet. The bounded native stdin route replaces that helper under the explicit contract.

## Governing source and original parent

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, `rules/design-authority.md`, the selected contract/admission, current snapshot/README, `yulang-lean-proofs` plus `references/sources.md` and `references/execution.md`, pinned configuration and relevant Lean README material.

Semantic source: authoritative annotation-effect-hygiene integration §§1, 1.1–1.2, 3–5; concrete annotation gate (permission creates no inflow; contribution siblings retain identity); top-level inference principles §1.1 and §§1–5. The annotation integration §6 correction withdraws the old callback output and is retained; no withdrawn output is used as a premise. The original parent is the source-preservation note §1, read with the authoritative birth-level SCC correction §§2–6. It quantifies over every supported original source program, lawful finite construction history and actual retained extrusion occurrence, preserves complete Call/effects/optional records/method selection, source scopes, original shared witnesses, soundness, required principal coverage, progress and termination. This finite private consumer result changes none of those quantifiers.

Exact parent Lean interfaces were read: `YulangClosure.SourceProblem.InferenceSoundness` is
`∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.
`SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence` and `InferenceTermination` remain separate. `YulangClosure.SourceProblem.native_success_elaborates` composes explicit `NativeCorrespondence`, `InferenceSoundness` and `Elaboration` with one scope/witness; neither that theorem nor `LocalLaws` constructs those concrete premises. The whole-proof closure manuscript §6 was read as a source map/research record, not semantic authority.

## Constructed model and exact source seam

`YulangClosure.AuthenticatedResidualConsumerR49.Step.physical` reuses R48 `EdgeReads` over exact current physical slots and owning R47 records. `Step.supportMember` instead checks `supportView`, the exact retained R48 view, native AnnotationMember view/ordinal, indexed family and `tail = none`. It carries no physical emission. `physical_path_iff` conservatively embeds old R48 paths; old `R48.extract` is unchanged. `lift_r48` uses exactly the same R45 query/probe/certificate, R47 entry query/probe and R48 query/terminal, explicitly adding closed-tail, candidate-inventory and selected-arm reads required for the new suppression consumer. Mixed paths use R49 authentication directly; they do not require the physical-only R48 extractor to accept logical steps.

`ArmReads` reads the actual Catch constructor and first arm at position 0, retaining Catch occurrence, edge-scrutinee identity, exact arm source/range, operation-pattern source, resolved full declaration/family, empty-call payload source and wildcard continuation. `unitSyntax` means HIR empty-call syntax, not an invented semantic Unit payload-matching law. The pattern types retain other payload/value constructors, but this private consumer accepts only the stated pattern. The original supported source domain remains the parent's unchanged domain.

`Authenticated` checks R45 extraction, R47 current entry matches, SAME use/fact/raw permission entry, selected family in the same permission, singleton provider/path inventories, complete checked mixed paths, R48 original slot-51 Catch reads and exact terminal provenance, terminal closure and exact arm reads. Candidate inventories are supplied owner reads: their agreement is checked, their Rust extraction/completeness is not proved. Each suppression in an accepted immutable plan yields the same witnesses via `accepted_suppression_applies` and `authenticated_prerequisites`; no aggregate source soundness law is assumed or proved by definition.

`providerCandidate` is partial: missing native/view/member reads are unavailable. Exact provider/declaration/member candidates need authentication and the unique terminal; other valid original endpoints forward. `plan_correspondence` preserves the complete ordered list and duplicate occurrences. `fold_correspondence` exposes exact native `(original endpoint, upper)` pairs. `unmatched_count` and `published_unmatched_count` preserve every distinct unmatched endpoint with multiplicity. `matching_gap_no_publication` and `unavailable_endpoint_blocks` rule out successful fallback/prefix publication in this pure projection. `publish` is an immutable trace projection, not a native mutation/rollback receipt.

Frozen Rust correspondence inspected: `candidate_receiver.rs` `LowerPathStep`/`certified_lower_paths`, `SelectedCatchArmEvidence`, `complete_residual_plan`, `publish_authenticated_residual`, `snapshot_suppression`, and source `assemble`. The frozen Rust handoff revision 1 and owner hashes below were verified. Its logical Support step, source arm provenance, prevalidated plan, selected-provider suppression and exact `constrain_live_effect(endpoint, upper, fact.id, fact.cause)` forwarding align with the represented fields. This is an inspected owner-path mapping, not a theorem extracting the model from every Rust state.

Represented: all existing R47 physical read checks; explicit finite mixed paths; exact R48 Operation terminal provenance; closed Support tails; finite source first-arm syntax/provenance; complete immutable plans; same-family foreign/other endpoints; arbitrary input list order/multiplicity. The concrete positive witness contains an actual checked logical Support step on both paths and forwards atom 8 twice at family 7 while suppressing provider atom 7. Finite negatives cover stale storage, reversed polarity, disconnected path, duplicate path/provider candidates, wrong arm, foreign provider/declaration, invalid/open Support reads and late failure before projected publication.

Omitted/unproved: source extraction completeness and key/allocation/lifetime fidelity; complete native search/visited/work-budget behavior; tail-edge root-ancestry beyond the reused per-edge live-owning checks; assembly/body/second-arm execution rules; payload byte-range validation (arm range is retained, payload source is retained); resource allocation/failure mutation semantics; all other ordinary compiler/source execution. R48 terminal path-list fields are retained for conservative physical lifting; mixed R49 path lists own the new logical evidence. No typing is defined as safety, no project axiom is introduced, and no concrete LocalLaws instance is claimed.

## Parent application and first remaining premise

Apply `accepted_suppression_applies c original out accepted endpoint suppressed` at each suppressed original endpoint: it reconstructs exact target equality, authenticated same R45 permission, checked R47 entry, common mixed-path R48 terminal/slot-51 evidence, actual source arm, and arrival to BOTH the internal entry and Catch input. Apply `publication_has_complete_plan` and `published_unmatched_count` to the same `c`, `original`, `upper` and published trace to preserve every unmatched original endpoint, including same-family siblings. No independently reselected permission, path or source witness appears.

First remaining premise/owner: the Rust/source lane must construct these exact owner-read inputs and complete singleton provider/path inventories from the same live `InferenceSession`/HIR snapshot, prove original terminal-list extraction and raw-key fidelity, and show the actual `constrain_live_effect` sequence realizes the pure fold. Concrete Rust build/runtime success is separately unobserved under this contract. The primary owns dispatch/review of those source/native obligations and the unchanged whole-source `InferenceSoundness`/coverage/elaboration/Catch-execution bridges. The existing source-law owners retain full subtraction/hygiene and A/B. No source-qualified counterexample to the parent was constructed; all these parent obligations remain OPEN.

## Verification and material failures

All theorem types and each complete transitive `#print axioms` result are retained in Audit 9 stdout below. There are 23 explicitly declared theorem roots in `YulangClosure.AuthenticatedResidualConsumerR49`. Final exit 0, no warnings/errors. `support_member_sound`, `lower_path_arrival`, `fold_correspondence` use `[propext]`; every other delivered theorem uses exactly `[propext, Quot.sound]`. No `Classical.choice`, `sorryAx`, project axiom or native-evaluation axiom occurs in the final root audits. Separate source scans of the changed dependency cone found no code-level `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `debug.skipKernelTC`.

The exact command for each stdin audit was `taskset -c 0 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, Python subprocess timeout 120 seconds. Input construction concatenates R39/R45/R47/R48/R49 in that order after removing only lines matching `^import YulangClosure[^\n]*\n`; `import Std` remains. The audit suffix sets `pp.universes`, `pp.fullNames`, `pp.funBinderTypes` true and, for each source-order theorem, runs `#check @YulangClosure.AuthenticatedResidualConsumerR49.NAME` and `#print axioms YulangClosure.AuthenticatedResidualConsumerR49.NAME`. No local `.olean` is imported. Native installed Std/kernel artifacts belong to the pinned distribution.

Material failed Lean calls retained in full: 1 (unsupported namespace alias syntax and `pp.width`, followed by elaboration fallout); 3 (doc comment immediately before `omit` was rejected); 5 (`cases` rewrote the existential goal, requiring reflexivity rather than the original `hp` equation). These are construction failures, not source counterexamples. Calls 2, 4, 6–9 exited 0; only final Audit 9 checks the frozen module. Source-model corrections after frozen Rust inspection additionally replaced a single-terminal-only decision with exact provider-origin classification, made malformed reads unavailable and included provider-candidate ambiguity checks. No failed receipt was erased.

Frozen module SHA-256: `ba9800813d2b005ec023971ac88798e1b4e41f2a93b971ddc025d8985c844ce0`.

Observed native version command/result:

```json
{
  "argv": [
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "--version"
  ],
  "exit": 0,
  "stdout": "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)\n",
  "stderr": "",
  "stdout_sha256": "eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
}
```

Pinned sources and frozen correspondence inputs:

```json
{
  "notes/design/2026-10-10-annotation-effect-hygiene-integration.md": "a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18",
  "notes/design/2026-10-10-concrete-effect-annotation-implementation.md": "3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae",
  "notes/design/2026-10-11-yulang-inference-top-level-principles.md": "7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81",
  "notes/design/2026-10-24-birth-level-scc-intrusion.md": "ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae",
  "notes/theory/2026-10-13-intrusion-source-preservation-proof.md": "3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271",
  "notes/theory/lean/YulangClosure/Contracts.lean": "2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e",
  "notes/theory/lean/YulangClosure/CoreComposition.lean": "1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c",
  "crates/yu-solver/src/candidate_receiver.rs": "4be3a60b382c9b294893e9a41c24818ad37aea8ed7ae4f9d337ce1f50fc9b7b3",
  "tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-rust.md": "aa9f7a2c28615850a4f78dcd6f35d38725e8a2a1104265f89e37506a2f9b8ae7",
  "notes/theory/lean/lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c",
  "notes/theory/lean/lakefile.toml": "212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4",
  "notes/theory/lean/lake-manifest.json": "058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3"
}
```

Aggregate measured Lean subprocess resources: {"audit_processes": 9, "wall_seconds": 51.80400029702287, "user_seconds": 39.043848, "system_seconds": 3.7129179999999997, "peak_child_rss_kib": 869976, "max_process_timeout_seconds": 120, "affinity_cpu": 0, "lean_memory_limit_mib": 1024}. Full agent active time, overall agent peak RSS and model/runtime telemetry UNKNOWN. Grant: at most 1800 seconds; no renewal or new resources requested. Each audit ran on one affinity CPU, `-j1`, `-M1024`, bounded timeout; every observed process exited in under 8 seconds.

Worker state: STOPPED. **WRITES STOPPED** after this frozen handoff write; no descendants or unaccounted generated paths. Independent review and primary integration remain pending. This is not self-certification, parent closure or production authority. Final handoff byte hash is reported to the primary outside this file.

## Actual stdin audit receipts

```json
{
  "call": 1,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 1,
  "elapsed_seconds": 7.741415014999802,
  "user_seconds": 3.809096,
  "system_seconds": 0.81478,
  "maxrss_kib": 834616,
  "input_bytes": 89868,
  "input_sha256": "39fb250bed70d4a72782f73eeeefb7292c531a726804b843708e64700d63fdd5",
  "stdout_sha256": "964b03aecd220e497522803a85047b873d8568dd140c3748abe9cbf13e3ff350",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "b923554244ced1b34b1b22fac3eaeb683166fd0c684ea5f4daddbb0d4e79fe11"
  }
}
```

Complete stdout:
```text
<stdin>:1382:14: error: unexpected token ':='; expected command
<stdin>:1383:14: error: unexpected token ':='; expected command
<stdin>:1384:14: error: unexpected token ':='; expected command
<stdin>:1392:9: error(lean.unknownIdentifier): Unknown identifier `R48.View`
<stdin>:1404:12: error(lean.invalidField): Invalid field `views`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.views`, so it is not possible to project the field `views` from an expression
  e.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1405:12: error(lean.invalidField): Invalid field `nativeAtom`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.nativeAtom`, so it is not possible to project the field `nativeAtom` from an expression
  e.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1405:40: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.annotationMember` could not be determined

Hint: Using `ProviderEntryArrivalR48.NativeAtom.annotationMember would be unambiguous:
  [apply] `ProviderEntryArrivalR48.NativeAtom.annotationMember`
<stdin>:1408:0: warning: declaration uses `sorry`
<stdin>:1412:22: error(lean.unknownIdentifier): Unknown identifier `R47.Probe`
<stdin>:1416:2: warning: declaration uses `sorry`
<stdin>:1415:4: warning: declaration uses `sorry`
<stdin>:1420:19: error(lean.unknownIdentifier): Unknown identifier `R48.EdgeReads`
<stdin>:1423:0: warning: declaration uses `sorry`
<stdin>:1423:0: warning: declaration uses `sorry`
<stdin>:1444:14: error(lean.invalidField): Invalid field `views`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.views`, so it is not possible to project the field `views` from an expression
  e.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1445:14: error(lean.invalidField): Invalid field `nativeAtom`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.nativeAtom`, so it is not possible to project the field `nativeAtom` from an expression
  e.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1445:42: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.annotationMember` could not be determined

Hint: Using `ProviderEntryArrivalR48.NativeAtom.annotationMember would be unambiguous:
  [apply] `ProviderEntryArrivalR48.NativeAtom.annotationMember`
<stdin>:1452:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.path_sound`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1464:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.lower_path_arrival`:
  [DecidableEq Artifact]
  [DecidableEq Id]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1472:19: error(lean.unknownIdentifier): Unknown identifier `R47.Probe`
<stdin>:1476:19: error: unsolved goals
case cons
Artifact Id Fact : Type
inst✝² : DecidableEq Artifact
inst✝¹ : DecidableEq Id
inst✝ : DecidableEq Fact
e : Inputs Artifact Id Fact
terminal : Endpoint Id
p : sorry
rest : List sorry
ih :
  ∀ (root : Endpoint Id),
    pathCheck e root (List.map Step.physical rest) terminal = pathCheck e.arrival root sorry terminal
root : Endpoint Id
⊢ (decide sorry && pathCheck e.arrival sorry sorry terminal) = pathCheck e.arrival root sorry terminal
<stdin>:1476:74: warning: declaration uses `sorry`
<stdin>:1476:74: warning: declaration uses `sorry`
<stdin>:1476:74: warning: declaration uses `sorry`
<stdin>:1476:74: warning: declaration uses `sorry`
<stdin>:1476:85: warning: declaration uses `sorry`
<stdin>:1520:42: error(lean.unknownIdentifier): Unknown identifier `R48.Query`
<stdin>:1527:38: error(lean.unknownIdentifier): Unknown identifier `R48.Query`
<stdin>:1539:19: error(lean.unknownIdentifier): Unknown identifier `R45.Inputs`
<stdin>:1540:18: error(lean.unknownIdentifier): Unknown identifier `R45.Query`
<stdin>:1541:18: error(lean.unknownIdentifier): Unknown identifier `R45.Probe`
<stdin>:1542:13: error(lean.unknownIdentifier): Unknown identifier `R45.Certificate`
<stdin>:1545:15: error(lean.unknownIdentifier): Unknown identifier `R47.Query`
<stdin>:1546:15: error(lean.unknownIdentifier): Unknown identifier `R47.Probe`
<stdin>:1547:10: error(lean.unknownIdentifier): Unknown identifier `R48.Query`
<stdin>:1553:2: error(lean.unknownIdentifier): Unknown identifier `R45.extract`
<stdin>:1554:2: error(lean.unknownIdentifier): Unknown identifier `R47.Matches`
<stdin>:1559:80: error(lean.invalidField): Invalid field `atom`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Probe.atom`, so it is not possible to project the field `atom` from an expression
  c.probe.terminal
of type `Probe Id`
<stdin>:1560:2: error(lean.unknownIdentifier): Unknown identifier `R48.CatchReads`
<stdin>:1561:88: error(lean.invalidField): Invalid field `atom`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Probe.atom`, so it is not possible to project the field `atom` from an expression
  c.probe.terminal
of type `Probe Id`
<stdin>:1562:2: error(lean.unknownIdentifier): Unknown identifier `R48.TerminalReads`
<stdin>:1565:0: warning: declaration uses `sorry`
<stdin>:1568:93: error(lean.invalidField): Invalid field `atom`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Probe.atom`, so it is not possible to project the field `atom` from an expression
  c.probe.terminal
of type `Probe Id`
<stdin>:1578:4: error(lean.unknownIdentifier): Unknown identifier `R47.extract`
<stdin>:1580:34: error(lean.invalidField): Invalid field `current`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.current`, so it is not possible to project the field `current` from an expression
  c.inputs.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1582:34: error(lean.invalidField): Invalid field `current`: The environment does not contain `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.Inputs.current`, so it is not possible to project the field `current` from an expression
  c.inputs.arrival
of type `Inputs Artifact Id Fact`
<stdin>:1584:4: error(lean.unknownIdentifier): Unknown identifier `R48.CatchReads`
<stdin>:1585:4: error(lean.unknownIdentifier): Unknown identifier `R48.TerminalReads`
<stdin>:1578:74: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
<stdin>:1581:43: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.effect` could not be determined

Hint: Using `RowKey.effect would be unambiguous:
  [apply] `RowKey.effect`
<stdin>:1603:16: error(lean.unknownIdentifier): Unknown identifier `R48.extract`
<stdin>:1605:16: error(lean.unknownIdentifier): Unknown identifier `R45.extract`
<stdin>:1604:11: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
<stdin>:1612:14: error(lean.unknownIdentifier): Unknown identifier `R48.accepted_iff`
<stdin>:1611:83: error: unsolved goals
Artifact Id Fact : Type
inst✝³ : DecidableEq Artifact
inst✝² : DecidableEq Id
inst✝¹ : DecidableEq Fact
Term : Type
inst✝ : DecidableEq Term
c : Context Artifact Id Term Fact
accepted : sorry = some sorry
internal : sorry = some c.internal
use : sorry = sorry
fact : sorry = sorry
raw : sorry = sorry
family : sorry ∈ sorry
entryTail : c.probe.entryTail = List.map Step.physical sorry
catchPath : c.probe.catchPath = List.map Step.physical sorry
arm : ArmReads c.source c.query c.probe.selection
⊢ authenticate c = true
<stdin>:1640:5: warning: Variable name `endpoint` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _endpoint

Note: This linter can be disabled with `set_option linter.unusedVariables false`
<stdin>:1646:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.suppression_iff`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1651:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.unmatched_decision`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1656:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.plan_correspondence`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1681:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.fold_correspondence`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1710:32: warning: This simp argument is unused:
  Ne.symm distinct

Hint: Omit it from the simp argument list.
  [apply] simp [fold, distinct, inductionResult]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1714:30: warning: This simp argument is unused:
  Ne.symm same

Hint: Omit it from the simp argument list.
  [apply] simp [fold, same, inductionResult]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1717:8: warning: declaration uses `sorry`
<stdin>:1728:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48.unavailable_no_publication`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1755:24: error(lean.unknownIdentifier): Unknown identifier `authenticated_prerequisites`
<stdin>:1752:98: error: unsolved goals
Artifact Id Fact : Type
inst✝³ : DecidableEq Artifact
inst✝² : DecidableEq Id
inst✝¹ : DecidableEq Fact
Term : Type
inst✝ : DecidableEq Term
c : Context Artifact Id Term Fact
original : List (Endpoint Id)
out : List (Endpoint Id × Decision)
accepted : plan c original = some out
endpoint : Endpoint Id
suppressed : (endpoint, Decision.suppress) ∈ out
decision : decideEndpoint c endpoint = some Decision.suppress
same : endpoint = target c
auth : authenticate c = true
⊢ endpoint = target c ∧
    Authenticated c ∧
      sorry = sorry ∧
        Arrival c.inputs endpoint (Endpoint.effectRow sorry) ∧
          Arrival c.inputs endpoint sorry ∧ ArmReads c.source c.query c.probe.selection
<stdin>:1759:0: error: Invalid name after `end`: Expected `R47.R48`, but found `YulangClosure.AuthenticatedResidualConsumerR49`

Hint: If you meant to end the outer scope(s) `YulangClosure.AuthenticatedResidualConsumerR49`, you must end all the intervening scopes `YulangClosure.AuthenticatedResidualConsumerR49.R45.R47.R48`:
  end YulangClosure.AuthenticatedResidualConsumerR49.̲R̲4̲5̲.̲R̲4̲7̲.̲R̲4̲8̲
<stdin>:1763:0: error: Unknown option `pp.width`
<stdin>:1764:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound`
<stdin>:1765:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound`
<stdin>:1766:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.path_sound`
<stdin>:1767:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.path_sound`
<stdin>:1768:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival`
<stdin>:1769:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival`
<stdin>:1770:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff`
<stdin>:1771:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff`
<stdin>:1772:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites`
<stdin>:1773:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites`
<stdin>:1774:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.lift_r48`
<stdin>:1775:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.lift_r48`
<stdin>:1776:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff`
<stdin>:1777:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff`
<stdin>:1778:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision`
<stdin>:1779:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision`
<stdin>:1780:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence`
<stdin>:1781:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence`
<stdin>:1782:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence`
<stdin>:1783:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence`
<stdin>:1784:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count`
<stdin>:1785:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count`
<stdin>:1786:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved`
<stdin>:1787:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved`
<stdin>:1788:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication`
<stdin>:1789:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication`
<stdin>:1790:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies`
<stdin>:1791:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies`

```

Complete stderr:
```text

```

## Audit 2

```json
{
  "call": 2,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 4.049683263001498,
  "user_seconds": 3.882597,
  "system_seconds": 0.206693,
  "maxrss_kib": 841876,
  "input_bytes": 90438,
  "input_sha256": "a7c4afd2e74f0de833d8defc25f290fb4b925f672338c46c7627db3c8b27797d",
  "stdout_sha256": "695c819cc219a376714f5438c74c4abbb8a0b586e9f67abec167e7707253248e",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "82de43a65e1394352f68c8928a1ec744f172a3c2ebdfd0e462bff4f192700cfa"
  }
}
```

Complete stdout:
```text
<stdin>:1438:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1449:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.path_sound`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1461:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1468:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1637:5: warning: Variable name `endpoint` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _endpoint

Note: This linter can be disabled with `set_option linter.unusedVariables false`
<stdin>:1678:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1707:32: warning: This simp argument is unused:
  Ne.symm distinct

Hint: Omit it from the simp argument list.
  [apply] simp [fold, distinct, inductionResult]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1711:30: warning: This simp argument is unused:
  Ne.symm same

Hint: Omit it from the simp argument list.
  [apply] simp [fold, same, inductionResult]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [DecidableEq.{1} Artifact] [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [DecidableEq.{1} Artifact]
  [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [DecidableEq.{1} Artifact] [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [DecidableEq.{1} Artifact] [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type} [DecidableEq.{1} Id]
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 3

```json
{
  "call": 3,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 1,
  "elapsed_seconds": 7.799754359002691,
  "user_seconds": 3.823822,
  "system_seconds": 0.83436,
  "maxrss_kib": 835736,
  "input_bytes": 91436,
  "input_sha256": "6d0a07813682326eb757e9dc44b86049ac9462575c01f20c9577ee112a5b791c",
  "stdout_sha256": "ef13761c1d97d0d99c9e977e002df2a5d747bfc9f5b0d50a5914e18d6ccd97e3",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "5bbd2f67024edad88b2d5548826c395e33bab2df6d2162ee456bb84b74a45e02"
  }
}
```

Complete stdout:
```text
<stdin>:1441:72: error: unexpected token 'omit'; expected '#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', 'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', 'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'recall', 'recommended_spelling', 'register_error_explanation', 'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', 'syntax', 'tactic_extension', 'theorem' or 'unif_hint'
<stdin>:1474:76: error: unexpected token 'omit'; expected '#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', 'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', 'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'recall', 'recommended_spelling', 'register_error_explanation', 'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', 'syntax', 'tactic_extension', 'theorem' or 'unif_hint'
<stdin>:1691:80: error: unexpected token 'omit'; expected '#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', 'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', 'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'recall', 'recommended_spelling', 'register_error_explanation', 'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', 'syntax', 'tactic_extension', 'theorem' or 'unif_hint'
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1}
                      (c.inputs.pathCandidates
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                      (List.cons.{0}
                        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                          c.probe.entryTail)
                        List.nil.{0}) →
                    Eq.{1}
                        (c.inputs.pathCandidates c.query.catchInput
                          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                        (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                      YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 4

```json
{
  "call": 4,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 7.955848051002249,
  "user_seconds": 4.080355,
  "system_seconds": 0.742251,
  "maxrss_kib": 846856,
  "input_bytes": 97667,
  "input_sha256": "ed36da0f3f31cf2cec971fb75f2308bdda81f53e76f9083309db5305f140ab75",
  "stdout_sha256": "8014ec05c9a4075c10c5047e95b51bd217f6300ff021f0981b65b4cf9f2614ef",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "b4ddaf5ec6e2d5adae22c6be6c63c4f510b17fb16f1ed4271c6a95833571126b"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1}
                      (c.inputs.pathCandidates
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                      (List.cons.{0}
                        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                          c.probe.entryTail)
                        List.nil.{0}) →
                    Eq.{1}
                        (c.inputs.pathCandidates c.query.catchInput
                          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                        (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                      YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 5

```json
{
  "call": 5,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 1,
  "elapsed_seconds": 4.690367391005566,
  "user_seconds": 4.516021,
  "system_seconds": 0.235124,
  "maxrss_kib": 867444,
  "input_bytes": 101385,
  "input_sha256": "a40dc21a33db3fad209c09dc4c871aabbc30c6cc72cd2bc977f10567decc24ba",
  "stdout_sha256": "959dfefd7a570f4f90df373c8bc2828f87f9c1d069ada2eaa91ba6e2e42b1643",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "a1e94c2dd4d91863cc03a58b5632ccba2816c1ce2c8e0ae6c465ec3c5885bbbe"
  }
}
```

Complete stdout:
```text
<stdin>:1871:16: error: Application type mismatch: The argument
  hp
has type
  plan c original = some out
but is expected to have type
  some out = some out
in the application
  And.intro hp
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1}
                      (c.inputs.pathCandidates
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                      (List.cons.{0}
                        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                          c.probe.entryTail)
                        List.nil.{0}) →
                    Eq.{1}
                        (c.inputs.pathCandidates c.query.catchInput
                          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                        (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                      YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}) },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query,
                probe :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                  { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                    selection :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                      { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                        armRange := __src.armRange, operationSource := __src.operationSource,
                        payloadSource := __src.payloadSource } } }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                    { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                      catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                      declaration := __src.declaration, family := __src.family },
                  probe := __src.probe }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                        declaration := 34, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                    YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                    (List.cons.{0}
                      (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                        { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                          ordinal := __src.ordinal, family := __src.family,
                          view :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                            { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                              tail := Option.some.{0} 35 } }))
                      List.nil.{0})
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                  Bool.false ∧
                Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.publish
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query := __src.query,
                      probe :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                        { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                          selection :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                            { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                              armRange := __src.armRange, operationSource := __src.operationSource,
                              payloadSource := __src.payloadSource } } })
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0}))
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 6

```json
{
  "call": 6,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 4.712560163003218,
  "user_seconds": 4.505691,
  "system_seconds": 0.267664,
  "maxrss_kib": 866060,
  "input_bytes": 101963,
  "input_sha256": "4eeac72e7c9c28cfc5f6fc6dcb03ba74e8b481409f90b100a8e0fa8230bf0d79",
  "stdout_sha256": "5cb6cd63ae6c4efacbc87f777042302a64153f0d9c6f570f779fa405072b444d",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "9d7b5d237809bbb35a75e7bbb2b996d6cd9f07dd57308a9146dfed23a1486d19"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                      (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                    Eq.{1}
                        (c.inputs.pathCandidates
                          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                        (List.cons.{0}
                          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                            c.probe.entryTail)
                          List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates c.query.catchInput
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                        YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                      (List.cons.{0}
                        (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                          { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                            ordinal := __src.ordinal, family := __src.family,
                            view :=
                              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                              { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                tail := Option.some.{0} 35 } }))
                        List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                    Bool.false ∧
                  Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query,
                        probe :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                          { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                            selection :=
                              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                              { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                armRange := __src.armRange, operationSource := __src.operationSource,
                                payloadSource := __src.payloadSource } } })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0}))
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 7

```json
{
  "call": 7,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 4.535584068005846,
  "user_seconds": 4.383851,
  "system_seconds": 0.20663199999999998,
  "maxrss_kib": 869540,
  "input_bytes": 103932,
  "input_sha256": "7c3aa33577a8dba07e491b02efec96cebddfbc5f3b409a8253fa96f917dac875",
  "stdout_sha256": "81af8500937adfacbb8d2573eccf26f5c2a7ef4c5af2dca43eb9a378e54bfabf",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "3f2bdcf5994ba7c05b6749f86ac062fc1b399bef23afee95a27db7383f098b2b"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
        (YulangClosure.AuthenticatedResidualConsumerR49.target c))
      Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} c.probe.terminal.view.tail Option.none.{0} →
                    Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                        (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0}
                            (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                              c.probe.entryTail)
                            List.nil.{0}) →
                        Eq.{1}
                            (c.inputs.pathCandidates c.query.catchInput
                              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                            (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                          YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) Bool.false →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
          (YulangClosure.AuthenticatedResidualConsumerR49.target c))
        Bool.true →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal,
                        inputs :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                          { arrival := __src.arrival, supportView := __src.supportView,
                            pathCandidates := __src.pathCandidates,
                            providerCandidates := fun (x x_1 x_2 : Nat) =>
                              List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query, probe := __src.probe })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0} ∧
                  Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                        YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                        (List.cons.{0}
                          (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                            { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                              ordinal := __src.ordinal, family := __src.family,
                              view :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                                { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                  tail := Option.some.{0} 35 } }))
                          List.nil.{0})
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                      Bool.false ∧
                    Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.publish
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                          query := __src.query,
                          probe :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                            { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                              selection :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                                { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                  armRange := __src.armRange, operationSource := __src.operationSource,
                                  payloadSource := __src.payloadSource } } })
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                            List.nil.{0}))
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 8

```json
{
  "call": 8,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 5.07322276999912,
  "user_seconds": 4.9443,
  "system_seconds": 0.194849,
  "maxrss_kib": 869976,
  "input_bytes": 104340,
  "input_sha256": "e9ac30ead551f05e7abe6e97e9c4e99832f486a3c42103afd1e7014da79119c7",
  "stdout_sha256": "032f94f1df014b858df4897c1195f379066c795123df130b0d93271a27967828",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "015c17986e3cce9f92cbafab8139048655eac2f720226afcff82f36ade878506"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
        (YulangClosure.AuthenticatedResidualConsumerR49.target c))
      (Option.some.{0} Bool.true)
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} c.probe.terminal.view.tail Option.none.{0} →
                    Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                        (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0}
                            (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                              c.probe.entryTail)
                            List.nil.{0}) →
                        Eq.{1}
                            (c.inputs.pathCandidates c.query.catchInput
                              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                            (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                          YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.false) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
          (YulangClosure.AuthenticatedResidualConsumerR49.target c))
        (Option.some.{0} Bool.true) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal,
                        inputs :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                          { arrival := __src.arrival, supportView := __src.supportView,
                            pathCandidates := __src.pathCandidates,
                            providerCandidates := fun (x x_1 x_2 : Nat) =>
                              List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query, probe := __src.probe })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0} ∧
                  Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                        YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                        (List.cons.{0}
                          (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                            { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                              ordinal := __src.ordinal, family := __src.family,
                              view :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                                { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                  tail := Option.some.{0} 35 } }))
                          List.nil.{0})
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                      Bool.false ∧
                    Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.publish
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                          query := __src.query,
                          probe :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                            { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                              selection :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                                { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                  armRange := __src.armRange, operationSource := __src.operationSource,
                                  payloadSource := __src.payloadSource } } })
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                            List.nil.{0}))
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 9

```json
{
  "call": 9,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 5.245565217002877,
  "user_seconds": 5.098115,
  "system_seconds": 0.210565,
  "maxrss_kib": 869664,
  "input_bytes": 106205,
  "input_sha256": "258a3953b6a4ded5ef919db873f3e61a043e8d4e2490a6e8365a747893818cb6",
  "stdout_sha256": "783734242d3e6a3649423a86cd026ec42697474bd4edb101176b8b18d03f0e75",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "ba9800813d2b005ec023971ac88798e1b4e41f2a93b971ddc025d8985c844ce0"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
        (YulangClosure.AuthenticatedResidualConsumerR49.target c))
      (Option.some.{0} Bool.true)
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} c.probe.terminal.view.tail Option.none.{0} →
                    Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                        (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0}
                            (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                              c.probe.entryTail)
                            List.nil.{0}) →
                        Eq.{1}
                            (c.inputs.pathCandidates c.query.catchInput
                              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                            (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                          YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.false) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
          (YulangClosure.AuthenticatedResidualConsumerR49.target c))
        (Option.some.{0} Bool.true) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal,
                        inputs :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                          { arrival := __src.arrival, supportView := __src.supportView,
                            pathCandidates := __src.pathCandidates,
                            providerCandidates := fun (x x_1 x_2 : Nat) =>
                              List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query, probe := __src.probe })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0} ∧
                  Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                        YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                        (List.cons.{0}
                          (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                            { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                              ordinal := __src.ordinal, family := __src.family,
                              view :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                                { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                  tail := Option.some.{0} 35 } }))
                          List.nil.{0})
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                      Bool.false ∧
                    Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.publish
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                          query := __src.query,
                          probe :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                            { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                              selection :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                                { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                  armRange := __src.armRange, operationSource := __src.operationSource,
                                  payloadSource := __src.payloadSource } } })
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                            List.nil.{0}))
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) Option.none.{0} →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.true) →
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∨
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```


## R50 current audit receipts

## Audit 10

```json
{
  "call": 10,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 8.559245263997582,
  "user_seconds": 4.704869,
  "system_seconds": 0.809788,
  "maxrss_kib": 865188,
  "input_bytes": 110329,
  "input_sha256": "682c8b07cef7d1e80a6fd76d0bb1d6ccdffb38ef2e918dbdf2a8f16812eaecb7",
  "stdout_sha256": "2bf023f9592e583702b524eb440ea2079432eb8752650f0b024779260dda5fb7",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "c2d311cb700b046efb259598a07c8b4d925b8b6a0f6d395ec09ffce2aee023d7"
  }
}
```

Complete stdout:
```text
<stdin>:1616:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.classification_match_iff`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1624:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.AuthenticatedResidualConsumerR49.classification_known_unmatched_iff`:
  [DecidableEq Artifact]
  [DecidableEq Fact]
  [DecidableEq Term]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Artifact] [DecidableEq Fact] [DecidableEq Term] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.classification_match_iff : ∀ {Artifact Id Fact : Type}
  [DecidableEq.{1} Artifact] [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact] {Term : Type} [DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch ↔
    YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads c ∧
      Eq.{1} c.probe.selection.declaration c.query.declaration ∧ Eq.{1} c.probe.selection.family c.query.family
'YulangClosure.AuthenticatedResidualConsumerR49.classification_match_iff' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.classification_known_unmatched_iff : ∀ {Artifact Id Fact : Type}
  [DecidableEq.{1} Artifact] [inst : DecidableEq.{1} Id] [DecidableEq.{1} Fact] {Term : Type} [DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched ↔
    YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads c ∧
      Ne.{1} c.probe.selection.declaration c.query.declaration
'YulangClosure.AuthenticatedResidualConsumerR49.classification_known_unmatched_iff' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_identity_match : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_identity_match' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
        (YulangClosure.AuthenticatedResidualConsumerR49.target c))
      (Option.some.{0} Bool.true)
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} c.probe.terminal.view.tail Option.none.{0} →
                    Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                        (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0}
                            (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                              c.probe.entryTail)
                            List.nil.{0}) →
                        Eq.{1}
                            (c.inputs.pathCandidates c.query.catchInput
                              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                            (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                          YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.false) →
    Ne.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.unavailable →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
        (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
          (YulangClosure.AuthenticatedResidualConsumerR49.target c))
        (Option.some.{0} Bool.true) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
            YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource, declaration := __src.declaration,
                          family := __src.family } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal,
                        inputs :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                          { arrival := __src.arrival, supportView := __src.supportView,
                            pathCandidates := __src.pathCandidates,
                            providerCandidates := fun (x x_1 x_2 : Nat) =>
                              List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query, probe := __src.probe })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0} ∧
                  Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                        YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                        (List.cons.{0}
                          (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                            { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                              ordinal := __src.ordinal, family := __src.family,
                              view :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                                { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                  tail := Option.some.{0} 35 } }))
                          List.nil.{0})
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                      Bool.false ∧
                    Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.publish
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                          query := __src.query,
                          probe :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                            { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                              selection :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                                { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                  armRange := __src.armRange, operationSource := __src.operationSource,
                                  payloadSource := __src.payloadSource, declaration := __src.declaration,
                                  family := __src.family } } })
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                            List.nil.{0}))
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) Option.none.{0} →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.true) →
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∨
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
            YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```

## Audit 11

```json
{
  "call": 11,
  "argv": [
    "taskset",
    "-c",
    "0",
    "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    "-j1",
    "-M1024",
    "--stdin"
  ],
  "cwd": "/home/momota1029/rust/yulang/notes/theory/lean",
  "timeout_seconds": 120,
  "exit": 0,
  "elapsed_seconds": 5.530344070997671,
  "user_seconds": 5.283244,
  "system_seconds": 0.316264,
  "maxrss_kib": 877876,
  "input_bytes": 119617,
  "input_sha256": "d4ac170074404781684896c0e914347a9b75d5eddf5c5f208a81b777eb3c7442",
  "stdout_sha256": "0b2057978b9b51658c4e574007ec8373daef71ddfc866fe0eb2c5a5138e52bb1",
  "stderr_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "source_sha256": {
    "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean": "4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2"
  }
}
```

Complete stdout:
```text
@YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Eq.{1} (Decidable.decide (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads e s)) Bool.true →
    Eq.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∧
      Eq.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∧
        Eq.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∧
          Eq.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∧
            Eq.{1} s.view.tail Option.none.{0} ∧
              YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member)
'YulangClosure.AuthenticatedResidualConsumerR49.support_member_sound' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.path_sound : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Id]
  (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root steps terminal) Bool.true →
    YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal
'YulangClosure.AuthenticatedResidualConsumerR49.path_sound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  YulangClosure.AuthenticatedResidualConsumerR49.LowerPath e root terminal →
    YulangClosure.AuthenticatedResidualConsumerR49.Arrival e terminal root
'YulangClosure.AuthenticatedResidualConsumerR49.lower_path_arrival' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (root terminal : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (steps : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Probe Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e root
      (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical steps) terminal)
    (YulangClosure.ProviderEntryArrivalR48.pathCheck e.arrival root steps terminal)
'YulangClosure.AuthenticatedResidualConsumerR49.physical_path_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.classification_match_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] {Term : Type}
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch ↔
    YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads c ∧
      Eq.{1} c.probe.selection.declaration c.query.declaration ∧ Eq.{1} c.probe.selection.family c.query.family
'YulangClosure.AuthenticatedResidualConsumerR49.classification_match_iff' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.classification_known_unmatched_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] {Term : Type}
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched ↔
    YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads c ∧
      Ne.{1} c.probe.selection.declaration c.query.declaration
'YulangClosure.AuthenticatedResidualConsumerR49.classification_known_unmatched_iff' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_identity_match : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_identity_match' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
        (YulangClosure.AuthenticatedResidualConsumerR49.target c))
      (Option.some.{0} Bool.true)
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_target_candidate' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true →
    Eq.{1} c.internal.permission c.internalProbe.permission ∧
      Membership.mem.{0, 0} c.internal.permission.concrete c.query.family ∧
        Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
            (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
          Eq.{1} c.entryQuery.use c.internal.use ∧
            Eq.{1} c.entryQuery.internalFact c.internal.fact ∧
              Eq.{1}
                  (YulangClosure.CurrentEmissionOwnershipR47.currentBound c.inputs.arrival.current
                    c.entryProbe.emission.physical)
                  (Option.some.{0} c.entryProbe.admission.bound) ∧
                Eq.{1} c.entryProbe.emission.physical.owner
                    (YulangClosure.CurrentEmissionOwnershipR47.RowKey.effect c.internal.permission.entry) ∧
                  YulangClosure.CurrentEmissionOwnershipR47.RelationPath c.inputs.arrival.current
                      c.entryQuery.rootRelation c.entryProbe.relation ∧
                    YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                        (YulangClosure.AuthenticatedResidualConsumerR49.target c)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                      YulangClosure.ProviderEntryArrivalR48.CatchReads c.inputs.arrival c.query ∧
                        YulangClosure.ProviderEntryArrivalR48.TerminalReads c.inputs.arrival c.query c.probe.terminal ∧
                          YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs
                              (YulangClosure.AuthenticatedResidualConsumerR49.target c) c.query.catchInput ∧
                            YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.authenticated_prerequisites' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.lift_r48 : ∀ {Artifact Id Fact : Type} [inst : DecidableEq.{1} Artifact]
  [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type} [inst_3 : DecidableEq.{1} Term]
  (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Eq.{1}
      (YulangClosure.ProviderEntryArrivalR48.extract c.inputs.arrival c.entryQuery c.entryProbe c.query
        c.probe.terminal)
      (Option.some.{0}
        { entry := { query := c.entryQuery, evidence := c.entryProbe }, query := c.query,
          evidence := c.probe.terminal }) →
    Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
        (Option.some.{0} c.internal) →
      Eq.{1} c.entryQuery.use c.internal.use →
        Eq.{1} c.entryQuery.internalFact c.internal.fact →
          Eq.{1} c.entryQuery.rawEntry c.internal.permission.entry →
            Membership.mem.{0, 0} c.internal.permission.concrete c.query.family →
              Eq.{1} c.probe.entryTail
                  (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                    c.probe.terminal.entryTail) →
                Eq.{1} c.probe.catchPath
                    (List.map.{0, 0} YulangClosure.AuthenticatedResidualConsumerR49.Step.physical
                      c.probe.terminal.catchPath) →
                  Eq.{1} c.probe.terminal.view.tail Option.none.{0} →
                    Eq.{1} (c.inputs.providerCandidates c.query.provider c.query.declaration c.query.family)
                        (List.cons.{0} c.probe.terminal.atom List.nil.{0}) →
                      Eq.{1}
                          (c.inputs.pathCandidates
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
                            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                          (List.cons.{0}
                            (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe)
                              c.probe.entryTail)
                            List.nil.{0}) →
                        Eq.{1}
                            (c.inputs.pathCandidates c.query.catchInput
                              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
                            (List.cons.{0} c.probe.catchPath List.nil.{0}) →
                          YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
                            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.lift_r48' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) ↔
    Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.true
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_iff' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.false) →
    Ne.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.unavailable →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
        (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
      ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
        Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.plan_correspondence' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out)
    (List.filterMap.{0, 0}
      (fun
          (item :
            Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision) =>
        match Prod.snd.{0, 0} item with
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress => Option.none.{0}
        | YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward =>
          Option.some.{0} (Prod.mk.{0, 0} (Prod.fst.{0, 0} item) upper))
      out)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_correspondence' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1}
          (List.count.{0} (Prod.mk.{0, 0} endpoint upper)
            (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
          (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (upper sibling : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
      (familyOf : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id → Option.{0} Id),
      Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) →
        Ne.{1} sibling (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
          Eq.{1} (familyOf sibling) (Option.some.{0} c.query.family) ∧
            Eq.{1}
              (List.count.{0} (Prod.mk.{0, 0} sibling upper)
                (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out))
              (List.count.{0} sibling original)
'YulangClosure.AuthenticatedResidualConsumerR49.same_family_sibling_preserved' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c
          (YulangClosure.AuthenticatedResidualConsumerR49.target c))
        (Option.some.{0} Bool.true) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
            YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_no_publication' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (out :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        YulangClosure.AuthenticatedResidualConsumerR49.Decision)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Membership.mem.{0, 0} out
          (Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
        Eq.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∧
          YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.accepted_suppression_applies' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Id] (e : YulangClosure.AuthenticatedResidualConsumerR49.Inputs Artifact Id Fact)
  (s : YulangClosure.AuthenticatedResidualConsumerR49.SupportMember Id),
  Ne.{1} (e.supportView s.support) (Option.some.{0} s.viewIndex) ∨
      Ne.{1} (e.arrival.views s.viewIndex) (Option.some.{0} s.view) ∨
        Ne.{1} (e.arrival.nativeAtom s.member)
            (Option.some.{0}
              (YulangClosure.ProviderEntryArrivalR48.NativeAtom.annotationMember s.viewIndex s.ordinal)) ∨
          Ne.{1} (GetElem?.getElem?.{0, 0, 0} s.view.allowed s.ordinal) (Option.some.{0} s.family) ∨
            Ne.{1} s.view.tail Option.none.{0} →
    Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck e
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.support)
        (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember s) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom s.member))
      Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.invalid_support_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  Ne.{1}
        (c.inputs.pathCandidates (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.entryQuery.rawEntry)
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
        (List.cons.{0}
          (List.cons.{0} (YulangClosure.AuthenticatedResidualConsumerR49.Step.physical c.entryProbe) c.probe.entryTail)
          List.nil.{0}) ∨
      Ne.{1}
          (c.inputs.pathCandidates c.query.catchInput
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom c.probe.terminal.atom))
          (List.cons.{0} c.probe.catchPath List.nil.{0}) ∨
        ¬YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false
'YulangClosure.AuthenticatedResidualConsumerR49.evidence_gap_rejected' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
    Bool.true ∧
  Eq.{1}
      (Decidable.decide
        (YulangClosure.AuthenticatedResidualConsumerR49.SupportReads
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport))
      Bool.true ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
          YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 4)
          YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
        Bool.true ∧
      Eq.{1}
          ((fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
              ite.{1}
                (Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) ∨
                  Eq.{1} endpoint (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
                (Option.some.{0} 7) Option.none.{0})
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8))
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query.family) ∧
        Ne.{1} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
            (YulangClosure.AuthenticatedResidualConsumerR49.target
              YulangClosure.AuthenticatedResidualConsumerR49.witnessContext) ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    List.nil.{0})))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_support_and_sibling_witness' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    Exists.{1}
      fun
        (out :
          List.{0}
            (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              YulangClosure.AuthenticatedResidualConsumerR49.Decision)) =>
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) (Option.some.{0} out) ∧
        Eq.{1} (List.map.{0, 0} Prod.fst.{0, 0} out) original ∧
          Eq.{1} constraints (YulangClosure.AuthenticatedResidualConsumerR49.fold upper out) ∧
            ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
              (decision : YulangClosure.AuthenticatedResidualConsumerR49.Decision),
              Membership.mem.{0, 0} out (Prod.mk.{0, 0} endpoint decision) →
                Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
                  (Option.some.{0} decision)
'YulangClosure.AuthenticatedResidualConsumerR49.publication_has_complete_plan' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (constraints :
    List.{0}
      (Prod.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) (Option.some.{0} constraints) →
    ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) →
        Eq.{1} (List.count.{0} (Prod.mk.{0, 0} endpoint upper) constraints) (List.count.{0} endpoint original)
'YulangClosure.AuthenticatedResidualConsumerR49.published_unmatched_count' depends on axioms: [propext, Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              {
                current :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessCurrent;
                  { artifact := __src.artifact, admissions := __src.admissions, emissions := __src.emissions,
                    valueRows := __src.valueRows, effectRows := fun (x : Nat) => Option.none.{0},
                    liveRelations := __src.liveRelations, dependencies := __src.dependencies,
                    relationPair := __src.relationPair, rootSource := __src.rootSource, sourceFact := __src.sourceFact,
                    rootCandidates := __src.rootCandidates, rootCause := __src.rootCause, rootTask := __src.rootTask,
                    rootCompleted := __src.rootCompleted },
                catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin, factPair := __src.factPair,
                nativeAtom := __src.nativeAtom, views := __src.views, sourceOperation := __src.sourceOperation },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    Bool.false ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
          source := __src.source, entryQuery := __src.entryQuery,
          entryProbe :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessEntry;
            { admissionIndex := __src.admissionIndex, emissionIndex := __src.emissionIndex,
              admission :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessAdmission;
                {
                  bound :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessBound;
                    { owner := __src.owner, polarity := YulangClosure.CurrentEmissionOwnershipR47.Polarity.negative,
                      item := __src.item },
                  relation := __src.relation },
              emission := __src.emission, relation := __src.relation, ancestry := __src.ancestry },
          query := __src.query, probe := __src.probe }))
      Bool.false ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
            query := __src.query,
            probe :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
              { entryTail := List.nil.{0}, catchPath := __src.catchPath, terminal := __src.terminal,
                selection := __src.selection } }))
        Bool.false ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
            { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
              internalProbe := __src.internalProbe, internal := __src.internal,
              inputs :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                { arrival := __src.arrival, supportView := __src.supportView,
                  pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                    List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps
                      (List.cons.{0} YulangClosure.AuthenticatedResidualConsumerR49.witnessSteps List.nil.{0}),
                  providerCandidates := __src.providerCandidates },
              source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
              query := __src.query, probe := __src.probe }))
          Bool.false ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                internalProbe := __src.internalProbe, internal := __src.internal,
                inputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                  { arrival := __src.arrival, supportView := __src.supportView, pathCandidates := __src.pathCandidates,
                    providerCandidates := fun (x x_1 x_2 : Nat) => List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                query := __src.query, probe := __src.probe }))
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query,
                  probe :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                    { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                      selection :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                        { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                          armRange := __src.armRange, operationSource := __src.operationSource,
                          payloadSource := __src.payloadSource, declaration := __src.declaration,
                          family := __src.family } } }))
              Bool.false ∧
            Eq.{1}
                (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                  (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                  { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                    internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                    source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                    query :=
                      have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                      { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                        catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := 33,
                        declaration := __src.declaration, family := __src.family },
                    probe := __src.probe }))
                Bool.false ∧
              Eq.{1}
                  (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
                    (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                    { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                      internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                      source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                      query :=
                        have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.query;
                        { catchOccurrence := __src.catchOccurrence, catchFact := __src.catchFact,
                          catchInput := __src.catchInput, catchOutput := __src.catchOutput, provider := __src.provider,
                          declaration := 34, family := __src.family },
                      probe := __src.probe }))
                  Bool.false ∧
                Eq.{1}
                    (YulangClosure.AuthenticatedResidualConsumerR49.publish
                      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                        internalProbe := __src.internalProbe, internal := __src.internal,
                        inputs :=
                          have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                          { arrival := __src.arrival, supportView := __src.supportView,
                            pathCandidates := __src.pathCandidates,
                            providerCandidates := fun (x x_1 x_2 : Nat) =>
                              List.cons.{0} 7 (List.cons.{0} 8 List.nil.{0}) },
                        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                        query := __src.query, probe := __src.probe })
                      (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    Option.none.{0} ∧
                  Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.pathCheck
                        YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 6)
                        (List.cons.{0}
                          (YulangClosure.AuthenticatedResidualConsumerR49.Step.supportMember
                            (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSupport;
                            { support := __src.support, member := __src.member, viewIndex := __src.viewIndex,
                              ordinal := __src.ordinal, family := __src.family,
                              view :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessView;
                                { origin := __src.origin, position := __src.position, allowed := __src.allowed,
                                  tail := Option.some.{0} 35 } }))
                          List.nil.{0})
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
                      Bool.false ∧
                    Eq.{1}
                      (YulangClosure.AuthenticatedResidualConsumerR49.publish
                        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                          internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
                          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                          query := __src.query,
                          probe :=
                            have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.probe;
                            { entryTail := __src.entryTail, catchPath := __src.catchPath, terminal := __src.terminal,
                              selection :=
                                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessSelection;
                                { catchOccurrence := __src.catchOccurrence, position := 1, armSource := __src.armSource,
                                  armRange := __src.armRange, operationSource := __src.operationSource,
                                  payloadSource := __src.payloadSource, declaration := __src.declaration,
                                  family := __src.family } } })
                        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                            List.nil.{0}))
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_authentication_failures' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) Option.none.{0} →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unavailable_endpoint_blocks' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Membership.mem.{0, 0} original endpoint →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} Bool.true) →
      Ne.{1} endpoint (YulangClosure.AuthenticatedResidualConsumerR49.target c) ∨
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.authenticate c) Bool.false →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
            YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch →
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original) Option.none.{0} ∧
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.matching_gap_no_publication' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_decision : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched →
    ∀ (candidate : Bool),
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint) (Option.some.{0} candidate) →
        Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
          (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
'YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_decision' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_plan : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched →
    (∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
        Membership.mem.{0, 0} original endpoint →
          Exists.{1} fun (candidate : Bool) =>
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint)
              (Option.some.{0} candidate)) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.plan c original)
        (Option.some.{0}
          (List.map.{0, 0}
            (fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id) =>
              Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
            original))
'YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_plan' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.fold_all_forward : ∀ {Id : Type}
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id)),
  Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.fold upper
      (List.map.{0, 0}
        (fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id) =>
          Prod.mk.{0, 0} endpoint YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
        original))
    (List.map.{0, 0}
      (fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id) => Prod.mk.{0, 0} endpoint upper)
      original)
'YulangClosure.AuthenticatedResidualConsumerR49.fold_all_forward' depends on axioms: [propext]
@YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_publish : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (original : List.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id))
  (upper : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
      YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched →
    (∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
        Membership.mem.{0, 0} original endpoint →
          Exists.{1} fun (candidate : Bool) =>
            Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate c endpoint)
              (Option.some.{0} candidate)) →
      Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.publish c original upper)
        (Option.some.{0}
          (List.map.{0, 0}
            (fun (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id) => Prod.mk.{0, 0} endpoint upper)
            original))
'YulangClosure.AuthenticatedResidualConsumerR49.known_unmatched_publish' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.unknown_identity_unavailable : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact),
  ¬YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads c →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.unavailable ∧
      Ne.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
          YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched ∧
        ∀ (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
          Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint) Option.none.{0}
'YulangClosure.AuthenticatedResidualConsumerR49.unknown_identity_unavailable' depends on axioms: [propext,
 Quot.sound.{u}]
@YulangClosure.AuthenticatedResidualConsumerR49.suppression_complete_authentication : ∀ {Artifact Id Fact : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Id] [inst_2 : DecidableEq.{1} Fact] {Term : Type}
  [inst_3 : DecidableEq.{1} Term] (c : YulangClosure.AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
  (endpoint : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Id),
  Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint c endpoint)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress) →
    Eq.{1} (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity c)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch ∧
      YulangClosure.AuthenticatedResidualConsumerR49.Authenticated c ∧
        Eq.{1} (YulangClosure.InternalPermissionIncidenceR45.extract c.internalInputs c.internalQuery c.internalProbe)
            (Option.some.{0} c.internal) ∧
          Eq.{1} (YulangClosure.CurrentEmissionOwnershipR47.extract c.inputs.arrival.current c.entryQuery c.entryProbe)
              (Option.some.{0} { query := c.entryQuery, evidence := c.entryProbe }) ∧
            Eq.{1} c.internal.permission c.internalProbe.permission ∧
              YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint
                  (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow c.internal.permission.entry) ∧
                YulangClosure.AuthenticatedResidualConsumerR49.Arrival c.inputs endpoint c.query.catchInput ∧
                  YulangClosure.AuthenticatedResidualConsumerR49.ArmReads c.source c.query c.probe.selection
'YulangClosure.AuthenticatedResidualConsumerR49.suppression_complete_authentication' depends on axioms: [propext,
 Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_known_unmatched_forwarding : YulangClosure.AuthenticatedResidualConsumerR49.IdentityReads
    YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext ∧
  Eq.{1}
      (YulangClosure.InternalPermissionIncidenceR45.extract
        YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.internalInputs
        YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.internalQuery
        YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.internalProbe)
      (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.internal) ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity
          YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.providerCandidate
            YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext
            (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
          (Option.some.{0} Bool.true) ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.authenticate
              YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext)
            Bool.false ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.plan
                YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0}))))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                        YulangClosure.AuthenticatedResidualConsumerR49.Decision.forward)
                      List.nil.{0})))) ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.publish
                YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext
                (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                  (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                    (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})))
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
              (Option.some.{0}
                (List.cons.{0}
                  (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                    (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                  (List.cons.{0}
                    (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 8)
                      (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                    (List.cons.{0}
                      (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
                        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
                      List.nil.{0}))))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_known_unmatched_forwarding' depends on axioms: [propext,
 Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_same_spelling_distinct_identities : Eq.{1}
    ((fun (x : Nat) => "ping")
      YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.probe.selection.declaration)
    ((fun (x : Nat) => "ping") YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.query.declaration) ∧
  Ne.{1} YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.probe.selection.declaration
      YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.query.declaration ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity
          YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext)
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.knownUnmatched ∧
      Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.publish
          YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext
          (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
          (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
        (Option.some.{0}
          (List.cons.{0}
            (Prod.mk.{0, 0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7)
              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
            List.nil.{0}))
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_same_spelling_distinct_identities' depends on axioms: [propext,
 Quot.sound.{u}]
YulangClosure.AuthenticatedResidualConsumerR49.concrete_r50_classification_boundaries : Eq.{1}
    (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity
      (have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext;
      { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
        internalProbe := __src.internalProbe, internal := __src.internal,
        inputs :=
          have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.inputs;
          {
            arrival :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
              { current := __src.current, catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin,
                factPair := __src.factPair, nativeAtom := __src.nativeAtom, views := __src.views,
                sourceOperation := fun (x : Nat) => Option.none.{0} },
            supportView := __src.supportView, pathCandidates := __src.pathCandidates,
            providerCandidates := __src.providerCandidates },
        source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
        probe := __src.probe }))
    YulangClosure.AuthenticatedResidualConsumerR49.Classification.unavailable ∧
  Eq.{1}
      (YulangClosure.AuthenticatedResidualConsumerR49.publish
        (have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext;
        { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
          internalProbe := __src.internalProbe, internal := __src.internal,
          inputs :=
            have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.inputs;
            {
              arrival :=
                have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessArrival;
                { current := __src.current, catchCandidates := __src.catchCandidates, factOrigin := __src.factOrigin,
                  factPair := __src.factPair, nativeAtom := __src.nativeAtom, views := __src.views,
                  sourceOperation := fun (x : Nat) => Option.none.{0} },
              supportView := __src.supportView, pathCandidates := __src.pathCandidates,
              providerCandidates := __src.providerCandidates },
          source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
          probe := __src.probe })
        (List.cons.{0} (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7) List.nil.{0})
        (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectRow 9))
      Option.none.{0} ∧
    Eq.{1}
        (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity
          (have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext;
          { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
            internalProbe := __src.internalProbe, internal := __src.internal, inputs := __src.inputs,
            source :=
              have __src := YulangClosure.AuthenticatedResidualConsumerR49.knownUnmatchedContext.source;
              { catchSource := fun (x : Nat) => Option.none.{0}, resolvedOperation := __src.resolvedOperation },
            entryQuery := __src.entryQuery, entryProbe := __src.entryProbe, query := __src.query,
            probe := __src.probe }))
        YulangClosure.AuthenticatedResidualConsumerR49.Classification.unavailable ∧
      Eq.{1}
          (YulangClosure.AuthenticatedResidualConsumerR49.classifyIdentity
            YulangClosure.AuthenticatedResidualConsumerR49.witnessContext)
          YulangClosure.AuthenticatedResidualConsumerR49.Classification.authenticatedMatch ∧
        Eq.{1}
            (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint
              (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
              {
                internalInputs :=
                  have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.internalInputs;
                  { artifact := __src.artifact, source := __src.source, formals := __src.formals,
                    constructions := __src.constructions, permissions := List.nil.{0}, receipts := __src.receipts,
                    plan := __src.plan, routeFact := __src.routeFact, lambdaRecipe := __src.lambdaRecipe,
                    componentTerm := __src.componentTerm, lambdaFact := __src.lambdaFact,
                    positiveFunctionChild := __src.positiveFunctionChild, negativeEntry := __src.negativeEntry },
                internalQuery := __src.internalQuery, internalProbe := __src.internalProbe, internal := __src.internal,
                inputs := __src.inputs, source := __src.source, entryQuery := __src.entryQuery,
                entryProbe := __src.entryProbe, query := __src.query, probe := __src.probe })
              (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
            Option.none.{0} ∧
          Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint
                (have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext;
                { internalInputs := __src.internalInputs, internalQuery := __src.internalQuery,
                  internalProbe := __src.internalProbe, internal := __src.internal,
                  inputs :=
                    have __src := YulangClosure.AuthenticatedResidualConsumerR49.witnessContext.inputs;
                    { arrival := __src.arrival, supportView := __src.supportView,
                      pathCandidates := fun (x x_1 : YulangClosure.CurrentEmissionOwnershipR47.Endpoint Nat) =>
                        List.nil.{0},
                      providerCandidates := __src.providerCandidates },
                  source := __src.source, entryQuery := __src.entryQuery, entryProbe := __src.entryProbe,
                  query := __src.query, probe := __src.probe })
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
              Option.none.{0} ∧
            Eq.{1}
              (YulangClosure.AuthenticatedResidualConsumerR49.decideEndpoint
                YulangClosure.AuthenticatedResidualConsumerR49.witnessContext
                (YulangClosure.CurrentEmissionOwnershipR47.Endpoint.effectAtom 7))
              (Option.some.{0} YulangClosure.AuthenticatedResidualConsumerR49.Decision.suppress)
'YulangClosure.AuthenticatedResidualConsumerR49.concrete_r50_classification_boundaries' depends on axioms: [propext,
 Quot.sound.{u}]

```

Complete stderr:
```text

```
