# EPM-MAT-r4/amendment02 source audit — bounded result, owners incomplete

Status: FROZEN; source worker STOPPED after this receipt. Independent review pending. Objective: determine whether the adopted ModuleEnv-Expose* rule's prerequisites are supplied by the pinned current owners of `ModuleNameSourceTypingAndAdmission` and `ModuleUseReceivingExportCorrespondence`. Method: authenticated full-file source/rule inspection and manual code-path derivation, without execution or theorem construction.

Baseline/dependencies: primary supplies `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, session `EPM-MAT-r4`, worktree `/home/momota1029/rust/yulang`. No Git lookup or mutation. New grant 350 seconds, fully charged with no refund/reuse. Prior r4 and r4a1 outputs and charges remain untouched, including r4's recorded cap overrun.

## Authentication and coverage

FIRST ACTION ran the primary's exact corrected r4a2 bootstrap command from repository root, before any new file-body reads. All twelve dispatched checksum entries reported OK; the pinned r3 Python preflight exited 0 and reported `PREFLIGHT_21_ENTRIES_ALL_MATCH`. Bootstrap manifest hash `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`; script hash `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`. The script path in both places was the undated `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py`.

All new body reads used separate tool responses, one file/page each, <=4096 raw bytes with `max_output_tokens:8192`. Command pattern: `/usr/bin/python3` with `Path(path).read_bytes()[start:end].decode()`. All pages decoded and arrived complete; truncations 0, retries 0. Metadata-only commands computed sizes/hashes and positions, without printing additional bodies. Every fully inspected file and reused governing file was rehashed unchanged immediately before receipt creation. Intervals below are half-open raw-byte ranges.

New COMPLETE coverage:

- `tasks/agent-loop/sprints/effect-permission-module-materialization-20261028-r4-amendment-02.md`: 5009 bytes; SHA-256 `3b8c408a97197777c0e40a9f293a35149d1ede70869c69f9ae53662060092f91`; pages [0,4096), [4096,5009); next EOF; COMPLETE.
- `notes/theory/2026-10-17-module-reference-materialization.md`: 28084 bytes; SHA-256 `f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb`; pages [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,20480), [20480,24576), [24576,28084); next EOF; COMPLETE.
- `notes/design/2026-10-17-module-environment-exposure-definition.md`: 3539 bytes; SHA-256 `d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d`; pages [0,3539); next EOF; COMPLETE.
- `notes/design/2026-10-16-module-expression-source-owner.md`: 8912 bytes; SHA-256 `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`; pages [0,4096), [4096,8192), [8192,8912); next EOF; COMPLETE.
- `notes/design/2026-10-17-module-entry-provenance-contract.md`: 6285 bytes; SHA-256 `44f33397a45f5d17a0302c6b1efbfe1f7bbdf018caed2ece2acc18176a746bd9`; pages [0,4096), [4096,6285); next EOF; COMPLETE.
- `notes/design/2026-10-17-accepted-call-hir-admission-contract.md`: 9670 bytes; SHA-256 `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`; pages [0,4096), [4096,8192), [8192,9670); next EOF; COMPLETE.
- `crates/yu-solver/src/candidate_call.rs`: 32230 bytes; SHA-256 `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`; pages [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,20480), [20480,24576), [24576,28672), [28672,32230); next EOF; COMPLETE.

Own complete governance reuse, authorized by amendment02 and reauthenticated against the frozen own r4 receipt (`4434dccb11598e88b6fa38c38895b19cfd7686f52b833df0698c683df632ea43`):

- `AGENTS.md`: SHA-256 `0ab35669cfc43ef1b3759ea81284a7f3b55bf3e030ab3aecb5bb32086a538c1d`; original complete r4 ranges [0,4096), [4096,8192), [8192,10937); next EOF; hashes reauthenticated, pages reused without reread.
- `AGENTS.pre-sprint.md`: SHA-256 `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562`; original complete r4 ranges [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,20480), [20480,23767); next EOF; hashes reauthenticated, pages reused without reread.
- `rules/goal-driven-sprints.md`: SHA-256 `e57c5c23e1956e09ea0da130a137ac50ce723ce5f0a90323adb17da88dab68b7`; original complete r4 ranges [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,19813); next EOF; hashes reauthenticated, pages reused without reread.
- `.agents/skills/yulang-lean-proofs/SKILL.md`: SHA-256 `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7`; original complete r4 ranges [0,4096), [4096,7856); next EOF; hashes reauthenticated, pages reused without reread.
- `rules/research-lab.md`: SHA-256 `1ffdabce7cc65d4e463e9a50a7a572c2974809bed415071b57a23efed8eb3228`; original complete r4 ranges [0,904); next EOF; hashes reauthenticated, pages reused without reread.
- `rules/design-authority.md`: SHA-256 `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`; original complete r4 ranges [0,4096), [4096,8192), [8192,10512); next EOF; hashes reauthenticated, pages reused without reread.
- `rules/git-concurrency.md`: SHA-256 `0992b73aea3fdd9a53c624b6010e1eeaa97d308f8f9e18698b9115d1b4cf8d09`; original complete r4 ranges [0,4096), [4096,8192), [8192,8795); next EOF; hashes reauthenticated, pages reused without reread.

The original r4 contract was completely read in r4 at [0,4096), [4096,7378); hash `12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f` reauthenticated by the new bootstrap. No proof-lane finding was adopted as evidence or body-read. Frozen receipts were authenticated as bootstrap dependencies only.

Explicit ZERO body coverage, next 0:

- `crates/yu-solver/src/candidate_source.rs`: 212009 bytes, 52 pages needed; hash `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- `crates/yu-solver/src/shadow_apply.rs`: 276524 bytes, 68 pages needed; hash `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
- `crates/yu-solver/src/lib.rs`: 1649811 bytes, 403 pages needed; hash `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.

These sizes/hashes were measured without body inspection. The primary explicitly acknowledged leaving these files unread if full EOF coverage cannot fit the grant and prohibited switching to function slices within this contract. All other manifest files have integrity validation only and no body coverage in this continuation. Their semantics are not used below.

## Exact adopted premise and authority boundary

The materialization note's initial UNADOPTED header is historical provenance; the separately inspected Authoritative adoption note selects its exact revision-2 formation and elimination clauses. This audit applies that accepted meaning without reopening it.

Materialization §3.1 [6518,7809) requires actual Pub/Fam/Mon/Ali/Liv owning derivations and complete dependent operands. Section 3.2 [7809,10529) requires original typed ambient/import environment E0, actual prior dependency publication derivations D_pub, original simultaneous registration Reg(C), resolved module-reference incidences I_C, and an already-lawful dependency-preserving source scope map theta_C. Section 3.3 [10529,14342) preserves constructors at exact binding-occurrence lookup and then applies that constructor's existing whole-map use rule. Missing original premises are not supplied by lookup, provider equality, native routes, or solver success. Unspecified import/capture/rebind edges remain unspecified.

The adoption note's Decision makes this static formation available, including the fixed dependency-prior Published use with identity ambient transport. Its Limits explicitly leave whole-source acceptance, registered ModuleContractRoot*, source Sig, native Phi_u and N-Transport unproved, and select no runtime/implementation representation. The rule's existence therefore does not by itself provide current Rust source/native data.

The fully inspected module-expression authority distinguishes authentic expression receiver routing and existing capture/FreshUse from whole typed-source materialization. The provenance contract is explicitly Draft, supplies representation requirements and historical locators, and closes zero original conditions. The HIR admission contract is also Draft and not adopted; its listed choices/old observations do not decide current global HIR behavior here. Neither draft is treated as new authority or current source-code evidence.

## Direct current-code evidence and conditional derivation

Only the fully inspected `candidate_call.rs` supports the following current-code conclusions. Function byte ranges and line anchors refer to its pinned 32230-byte body:

- `ApplySourceInput` [1311,2187), line 39, retains owner, Apply/callee/argument positions, levels/recipe, endpoint/effect/result positions, checking/cause and optional formal/local/native/introduction/receiver attachments. This struct is an input inventory; it is not an E0/D_pub/Reg(C)/theta_C source derivation.
- `PendingCallSupplier` [6622,6970), line 179, explicitly declares both module obligations as missing compiler suppliers, separate from semantic residual constraints.
- `CandidateSourceCall::module_callee_target` [12909,13204), line 314, pattern-matches only its direct callee's `LocalSourceForm::Name { resolution: ModuleDef(target), .. }` and returns `Some(target)`; all other forms return None. It constructs no typed entry, lawful source scope map or introduction certificate.
- `PendingCallConstruction::suppliers` [16493,17672), line 407, computes `module_callee = module_callee_target().is_some()` and guards BOTH module supplier entries with exactly that Boolean. There is no local discharge operation in this iterator.
- `observe_inner` [19896,27746), line 487, validates retained Apply/callee/argument indices, checking/cause provenance, occurrence and scope ownership, native demand Function/ports/row, plus optional formal/introduction/receiver attachments. It returns a borrowed CandidateSourceCall. Its inspected validations are not a construction of the adopted typed module environment/lookup derivation or a complete source-to-native receiving/export map.
- `authenticate_scoped_apply` [28263,31879), line 698, validates the Local-callee FreshUse route when such a route is encountered; its final other-form branch returns according to whether `input.local_callee` is absent. This function does not itself supply the module environment premises. This is a bounded function observation, not a claim about called helpers or all native routing.

Conditional code-path derivation (manual inspection, no executable run):

1. Assume c is a successfully produced CandidateSourceCall whose direct `callee.form` is Name with ModuleDef(t). Do not assume such a c is produced for every source program or accepted by ordinary HIR.
2. The exhaustive match in module_callee_target returns Some(t), so module_callee is true.
3. The two named module entries in suppliers have needed=true. On exhausting the returned iterator, filter_map therefore yields both `ModuleNameSourceTypingAndAdmission` and `ModuleUseReceivingExportCorrespondence`.
4. This conclusion is independent of whether `c.formal` is Some or None. If formal=None, the exact output is the three always-requested suppliers OriginalGenCall0, ArgumentReifyAndWholeCarrier, ReceiverDispatchAndCompleteResultFutureInterfaces, followed by the two module suppliers. If formal=Some, the three formal suppliers precede those five.

This is a bounded conditional characterization of this source observer/iterator under ordinary Rust match/iterator semantics, with the supplied c and iterator exhaustion as explicit hypotheses. It is not a source-qualified counterexample, a theorem of language acceptance, or evidence that every external consumer handles these requests correctly. Wrapped module expressions do not satisfy the direct-match hypothesis; no conclusion about their external admission/handling is made.

## First unsupported edge and disposition

For `ModuleNameSourceTypingAndAdmission`, the first unsupported edge in the inspected evidence is from the authentic structural ModuleDef callee/DefId to an actual typed module entry and exact occurrence lookup derivation under E0/D_pub/Reg(C)/I_C/theta_C, followed by the genuine branch-specific Name/use rule and source admission. The adopted rule states what this requires; the inspected current observer supplies target identity and structural/native-port validation and continues requesting the supplier. No inspected artifact supplies that source derivation for the actual observed call. A lawful scope map is not established merely by `scope_owned` returning true.

For `ModuleUseReceivingExportCorrespondence`, the iterator independently requests the supplier. The native interface fields retain endpoints, not an inspected fieldwise interpretation of the selected source entry and whole reference/allocation map into the receiving/export operation. Because current candidate_source/shadow_apply/lib bodies are unread, native routing/receiving/export correctness or absence is UNVERIFIED here. Historical note descriptions of `execute_candidate_action`, `route_candidate_open_use` and `route_incoming` are locators only.

Claim class: established adopted-rule premise inventory plus a manual bounded conditional code-path derivation. Neither supplier is discharged by this audit. It does not establish global nonexistence of a source owner, does not independently reconstruct source Sig/Phi_u, and does not claim either supplier is impossible. This is a precise inspected-evidence gap, not proof that unseen code lacks the missing fields or behavior.

Original source domain, all ambient indices/assignments, shared witnesses, joint strategies, guards, arbitrary well-scoped clients and native obligations remain unchanged. Nothing closes callback -> Call result -> tuple left, original A/B, complete Call/effects, soundness/principality/termination or production. `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding. Overall source/native audit INCOMPLETE; bounded inspected result ready for fresh review.

## Oracle independence, omissions and resources

There was no semantic oracle, executable transition model, seed sweep, mutation experiment, build/test or Lean check. Hash/preflight independence is limited to byte equality against the primary's manifest; it shares the manifest/dispatch assumptions and cannot establish semantic source rules. The conditional derivation inspects actual current code rather than an assumed toy transition system, but assumes ordinary Rust interpretation and does not prove compiled/runtime correspondence. No independent review of this own output is claimed.

Failure conditions for the bounded derivation: changed pinned bytes; c outside the direct ModuleDef match; a caller not exhausting the iterator; failure of the assumed successful observation; or behavior supplied by an external consumer outside this inspected file. Failure of the full supplier inference is already explicit: authentic entry/lookup/admission and native whole-map correspondence are not established by these inspected artifacts. Unsupported forms, imports/captures/rebinds, recursive and alias branch formation, receiving/export, rollback/replay and all current source/native owner paths remain outside checked implementation coverage.

One lightweight command process at a time; no descendants, source edits, tests, Cargo, builds, Lean, Git, background work or temporary files. First explicit wall-clock sample: Unix 1793161035.2888498 (after bootstrap). Freeze-preparation sample: Unix 1793161277.3868554; measured lower-bound interval 242.098 seconds. Startup/dispatch-to-first-sample interval is UNKNOWN, so no precise full-elapsed claim. Stopping with substantial measured headroom rather than beginning 120 additional pages. CPU/peak RSS uninstrumented. Full 350-second grant charged, no refund/reuse. Writer stops after final receipt creation/hash report.

Recommended next action: primary admit one owner-audit packet with an explicit bounded coverage unit (for example authenticated complete function snapshots plus required declarations) for the actual module Name producer and receiving/export consumer, or grant sufficient resources for whole-file coverage. Ask it to supply/refute the exact typed-entry/lookup/admission and fieldwise native-map edges above; keep semantic choices fixed and every production gate OPEN.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-module-materialization-r4a2-source.md` only.
- Baseline SHA: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (primary supplied).
- Dependency hashes changed: none among fully inspected/reused files, rechecked before writing; all 21 manifest entries matched during bootstrap. Unread implementation bodies have no semantic result and were not reread at freeze.
- Review status: frozen, fresh independent review pending; no own-output certification.
- Checks run: exact twelve-entry bootstrap, pinned 21-entry preflight, complete bounded pages above, governing/full-read metadata revalidation, metadata-only position calculations. No executable semantic check/test/build.
- Proposed one-line research-checkpoint message: `research: bound adopted module rule to pending Call suppliers`.
- Shared-record deltas intentionally left for primary/curator: acknowledge stopped/frozen source receipt and full 350-second charge; record complete rule/notes/candidate_call coverage with zero large-owner coverage; retain both supplier gates and all original/native/production gates OPEN; review the conditional source-path result without promoting it to owner completeness. Preserve prior r4 overrun, r4a1 authentication failure, frozen receipts and unknown leases/quarantines.
