# R118 independent static review

Verdict: **ACCEPT only as a CONSTRUCTED/UNCHECKED finite candidate and the source-grounded obstruction allowed by R118 outcome (b).** No BLOCKING, major or minor defect established in the submitted local theorem statements. The bridge below remains BLOCKING for a claim of R116 instantiation or source/native/production closure; it is explicitly disclosed by the submission and is not a newly concealed assumption.

Assignment `/root/r118_review`, bounded at 180 seconds, no descendants. Applied the `yulang-lean-proofs` source/premise review discipline; explicit packet execution prohibition overrides its normal checker steps. No Lean/Lake/checker/compiler/build/test or environment exploration was performed. Static plausibility does not establish elaboration or kernel acceptance.

## Frozen identity and independent method

Independently recomputed SHA-256, all shell exits 0:

| Input | SHA-256 |
| --- | --- |
| R118 Lean | `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` |
| R118 proof handoff | `fa4fcadbf028846469897aa815df4f58a9daeff58740f04891efde651edf6e79` |
| R117 patch | `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` |
| R117 Rust handoff | `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e` |
| R117 review2 | `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664` |
| R39 | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R45 | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| R54 | `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9` |
| R116 | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |

Read the Lean submission, contract, exact dependency definitions and frozen patch before using the R118 author's handoff. Independently read relevant Rust only through immutable `git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:<exact path>` for candidate_effect.rs, candidate_source.rs and candidate_receiver.rs. No dirty Rust file was accessed. Read receiver tests at pinned lines 5703–5794: signal suppression, same-spelling write forwarding, grouped scrutinee, and private-envelope admission controls. They provide intended sibling behavior, not executed evidence or coverage of this new decoder model.

Governing scope: R118 contract fixed outcome and outcome (b); Authoritative annotation/effect integration §§1–1.2 and inference principles §1.1; R39 constructor definitions; R45 exact OwnerReads/Identity; R54 full owner identity; R116 selected-source/operation/constructor premises. Original `Contracts.lean:128–130` quantification and whole-proof closure scope remain unchanged.

## Actual theorem surface

All names below are in `YulangClosure.NativePermissionDecoderR118`; all remain CONSTRUCTED/UNCHECKED, with actual printed types and complete axiom sets UNKNOWN.

- `contains_member` (38–47): arbitrary decidable identity type, list and family, with `contains xs family = true`; concludes list membership. Recursive equality branch is the supplier, not a membership assumption. Duplicates/order are retained.
- `read_family_exact` (77–88): successful read of the supplied inventory implies both the ordinal-tagged view read and actual member read. No conversion of a member coordinate into a family identity occurs.
- `read_permission_exact` (90–106): successful registration-keyed read implies an exact singleton filtered inventory at the separately supplied storage coordinate. Missing/duplicate registrations and mismatched storage are rejected by the definition.
- `decode_member` (110–140): arbitrary decidable family, state and batch types; only substantive premise is success of the explicitly partial decoder. Concludes equality of both owner components, exact view/member read, exact singleton retained selection and family membership in that selected value. It does not assume R39 preparation/retention, R45 extraction, selected source, operation identity or membership.
- `unequal_coordinates` (144–150): the finite permission with registration 1 is stored at 0; native member 1 reads family 7. The explicit inequalities distinguish registration/storage and member/family. The example does not claim all four coordinates are pairwise unequal or source-derived.
- `post_state_is_not_prepare_input` (154–161): local decoder success coexists with failure of R39 prepare on a state whose retained-registration set contains 0. Its `by decide` text has not executed.

Static branch inspection found no use of a project axiom, sorry/admit or checker bypass in R118. This source search is not an indirect axiom audit.

## Counterexample and alternate-path attacks

The change isolates the responsible read/guard boundary, then identifies the temporal constructor obligation at its source owner. It does not claim a downstream membership guard repairs source construction.

1. Registration 1 in compact slot 0 passes; changing the supplied storage to 1 fails. Adding another permission with registration 1 fails regardless of equality of family payloads. The R117 patch searches by record registration in both capture and consumer, while the separate formal table remains registration-indexed.
2. An absent view/member or mismatched stored view ordinal fails `readFamily`. A different member can succeed only if its actual stored value passes the permission guard. No equality between a Nat index and arbitrary Id is assumed.
3. Different state with equal batch, or equal state with different batch, fails `decode` because it compares the full R54 owner. However, the lists are externally supplied and not intrinsically owned: assigning equal owner labels to foreign lists can pass. The submission accurately leaves Rust pointer-to-value interpretation open; this cannot authenticate foreign inventory provenance by itself.
4. Same family with distinct operation identity can pass this partial model because it has no operation argument. The R117 patch independently rejects it with full operation/declaration guards; R116 operationMatch requires full identity/declaration/family equality. R118 explicitly omits these guards and does not assert successful Suppress or complete decoder acceptance, so this is a boundary of the claim, not a counterexample to `decode_member`.
5. Equal-looking copied permissions can pass this value model. Actual R117 pointer/slice checks remain additional guards. `read_permission_exact` proves the supplied inventory value was selected, not that it is R45's probe permission or R116's original source-row copy.
6. Post-state success cannot supply pre-state nonmembership: R39 Valid at 116–122 requires registration absent; pinned Rust candidate_effect.rs:1780–1781 checks absence before publishing at 1818–1821. Keeping the resulting record and later decoding its family leaves that absence false in the post-state.

No AST/CST, propagation, restoration or diagnostic change is introduced here. Failed reads return none in the local model; absence of the other Rust guards prevents interpreting none/some as the full observer or inference result. No rollback or recovery theorem is claimed. Open input containing write, symbolic flow, other annotations, continuation and nested source cases remain in the parent domain; this module proves no result for them and removes none from that domain.

## BLOCKING remaining bridge for parent application

**Locations:** R118:14–19, 67–75, 154–161; R39:116–136; R116:110–119 and 134–147. Actual pinned suppliers: candidate_source.rs:1323–1327 constructs Action::FormalEntry from the Lambda parameter annotation; candidate_effect.rs:1763–1783 reads the row/formal/source owner/Lambda and pre-state absence guards, 1786–1802 copies permission fields, and 1818–1821 publishes the record.

**Concrete obstruction:** decoder success provides no earlier Action or source row and no authentic pre-constructor state. The post-state falsifier above prevents reusing the retained inventory as R39 Inputs with its absence condition. Inventing an empty retained-registration list would repair the observed guard syntactically while leaving correspondence unproved.

**Invariant:** R118 prohibits assumed prepare/permissionFor/extract or a generic faithful decoder from closing the bridge. R116 requires the SAME source row/action/permission and the full selected-operation relation. R45 additionally requires its exact owner/formal/recipe/route/slot-2/positive Function/negative entry reads. R54 requires actual state and batch identity. Whole-language soundness must retain the original source scope and shared witness.

**Minimum closure evidence:** reconstruct the actual constructor event/pre-state and exact source Action/annotation/owner-local Lambda; derive both R39 equations and stable identity of the retained record. Separately interpret pointer/slice and coordinate reads, derive SelectedSource and operationMatch for the selected arm, and construct all R45 OwnerReads/Identity so its output permission is the same selected value. These are source/native obligations, not assumptions supplied by `decode_member`. Kernel validation plus full actual axiom reports will also be needed under a separately authorized execution envelope. No extra semantic clause or reduced source domain is justified by this review.

Thus R118 has not instantiated either R116 theorem. It supplies the finite read/any consequence and a concrete first obstruction, satisfying the contract's alternative (b). Original inference soundness, effect hygiene, principality, termination, native correspondence and production remain OPEN.

## STOP receipt

Only this exact review receipt was written. No source, import, shared state, dependency, Git index/ref, scratch/temp/cache/worktree or other lane output was changed. No descendants or generated outputs. No tests/checkers/builds/toolchain commands or environment probes were run. Read commands and sha256sum exited 0. Writes STOPPED at this receipt freeze; hash reported externally to avoid a self-hash cycle.
