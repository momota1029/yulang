# R119 proof handoff — revision 1, CONSTRUCTED / UNCHECKED

Sprint `EFFECT-PERMISSION-MEMBER-WITNESS/20261102-R119`, contract revision 2 SHA-256 `c499fe513f2c6915049775affe5b159ae0ecdc971b172962b85dc3aaa95fc40a`. Assignment `/root/r119_proof`; sole author, no descendants. Exact leases: `notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean` and this handoff. Requested/observed model and effort UNKNOWN; actual CPU, RSS and runtime UNKNOWN (uninstrumented). Finite bound: 300 seconds, no renewal. Outcome class: conditional candidate. Independent review, kernel acceptance, source/native correspondence and production authority are not established.

## Authority, original parent and scope

Read root AGENTS, base operating map, goal-driven sprint rules, proof skill and its source/execution references, current state, handoff protocol and fixed R119 packet. Packet prohibition on execution controls over the skill's ordinary checker workflow. No installation or verification environment was attempted.

Authoritative policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, SHA `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`, with `2026-10-11-yulang-inference-top-level-principles.md` §1.1. Contravariant `[signal]` grants local subtraction; compatible `[signal, write]` input remains admitted and write remains outward. Concrete identities include resolved arguments. Permission, actual inflow and residual are distinct.

Original parent `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128` (SHA `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`):

`∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.

`docs/yulang-whole-proof-closure-ja.md` §§1,3–4 (SHA `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`) retains the full source scope, original lexical scope and one shared witness. Its opening birth-level SCC correction remains in force. The integration draft grants no new semantics or source restriction. R119 neither proves this proposition nor constructs a concrete LocalLaws instance.

Local parent: R116 `selected_endpoint_member` requires the SAME R39 `prepare` and `permissionFor` equations, source row/selected arm, operationMatch and endpoint-family equation; `internal_certificate_member` additionally requires R45 extract on that SAME permission. Actual definitions were read. R39 Valid requires absence of the registration in the PRE-state; its permissionFor rejects only empty concrete rows for retention, without rejecting their source admission. R45 accepted_payload transports precisely probe.permission. R54 Owner retains state AND batch identity. R118's POST-state counterexample remains an obstruction to reusing POST data as the PRE constructor input.

## Frozen dependencies

These actual byte hashes were recomputed using `sha256sum`:

| Input | SHA-256 |
| --- | --- |
| R118 `NativePermissionDecoderR118.lean` | `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` |
| R118 proof handoff | `fa4fcadbf028846469897aa815df4f58a9daeff58740f04891efde651edf6e79` |
| R118 independent review | `bee20cccf34f82388f5f68836e95865c1f878381c45f0fa7df7a95cce8d0ef7b` |
| R117 patch, `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch` | `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` |
| R117 Rust handoff revision 2 | `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e` |
| R117 independent review 2 | `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664` |
| R39 `ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R45 `InternalPermissionIncidenceR45.lean` | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| R54 `OwnedResidualProjectionR54.lean` | `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9` |
| R116 `SuppressionPermissionR116.lean` | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |

The initial contract locator produced a missing-file read/hash failure (sha256sum exit 1). Primary explicitly corrected the locator in contract revision 2; the artifact path above exists and independently matches the pinned SHA. This failure was a locator defect, not a Lean diagnostic. No dirty Rust source or immutable Git blob was read by this worker; only the frozen patch and handoffs/reviews were used for Rust context. Baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` is an inherited contract pin, not independently queried Git evidence.

## Constructed declaration types and application

Artifact SHA-256: `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`.

All six names have prefix `YulangClosure.PermissionMemberWitnessR119.`; these are descriptions of written source types, NOT printed Lean results:

- `search_index_read`: for arbitrary decidable `Id`, list xs, family and member, successful recursive orderedSearch xs family = some member implies xs[member]? = some family. Recursion returns the first equality position, preserving order and duplicates.
- `indexed_read_member`: for arbitrary list/index/identity, a successful indexed read constructs membership by list/index induction.
- `same_record_search_read`: ordered search of permission.concrete for searchedFamily at permissionMember, AND consumption of permission.concrete at that same index as consumedFamily, imply consumedFamily = searchedFamily and searchedFamily membership. Search supplies the expected value, read supplies the observed value; Option injectivity joins them. Neither membership nor a decoder law is assumed.
- `selected_retained_member`: applies that join to the exact permission returned by R118 readPermission and the family returned by R118 readFamily. Returns exact native view/member reads, singleton registration-filtered retained selection at its separate packed slot, equality of consumed/provider families, and provider membership in the same permission. The permission-member argument is separate from endpoint.member, registration and storage.
- `certificate_member_if_extracted`: applies the join to probe.permission, then R45 accepted_payload transports membership to out.permission under the original explicit extract equation. This is a conditional application, not a construction of extract's premises or a substitute for R39 provenance.
- `distinct_coordinates_and_duplicates`: finite candidate with registration 7, packed slot 0, permission vector [4,9,9] whose search for 9 returns index 1, and native endpoint member 0 reading 9. Registration/storage/member/family are not identified. Its written `by decide` has not run.

No project axiom, hole or checker bypass was introduced. No membership hypothesis, generic faithful decoder, source-typing redefinition or LocalLaws parameter supplies membership. Empty lists fail the ordered search; duplicate identities preserve the first successful position. Arbitrary list lengths/identity types are retained. This module defines no source language and excludes no accepted source constructor.

## Remaining operational and parent premises

The finite result applies only after actual values have been interpreted. First native obligation, owned by the private decoder/projection source owner and primary: show Rust iter().position produces this orderedSearch index; it is carried unchanged through projection/request; concrete.get reads that index from the very same retained record/vector; immutable borrows and pointer/slice checks authenticate that sameness. List-value equality alone cannot certify physical identity, owner/state/batch, allocation or foreign records. Full resolved operation/provider/arm identity, view/member lookup and integer conversion checks must also be interpreted. Successful local reads are not full Suppress acceptance or source admission.

Separately OPEN, owned by the R39 source-constructor/proof lane via primary: reconstruct the actual earlier Action::FormalEntry, exact annotation/row, owner-local Lambda and authentic PRE Inputs; derive prepare and permissionFor for the same retained record. POST membership supplies no PRE nonregistration evidence. R45's full OwnerReads/Identity and extraction are still required, as are R114 admission transport and the original source-to-generation/propagation/native links. The conditional certificate theorem does not discharge them.

Thus the same-record finite membership fact is constructed, while R116 concrete source instantiation, original inference soundness, complete hygiene, principality, termination and production remain OPEN. Open [signal,write] flows, callback/computation annotations, polymorphism, symbolic variables, nested handlers, continuation behavior and all other source cases remain in the parent scope; no source/native theorem for those cases is delivered here.

Mutual TODO `R119-AUTHENTICATE-MEMBER-TRACE-1`: primary joins the independently reviewed R119 Rust candidate to these exact field/list interpretations, including an earlier unannotated formal followed by registration 7 at compact slot 0, duplicates, foreign record/state and changed-index falsifiers. Required output is an authenticated operational correspondence or a precise rejected trace, not another assumed membership law. R39 PRE reconstruction remains a separate TODO, not merged into this request.

## Checks, resources and STOP

Actual commands: read-only cat/sed/rg and sha256sum; source-read/hash commands succeeded except the preserved initial missing locator. Final corrected artifact hash command exited 0. apply_patch wrote only the two leased outputs. No Lean/Lake/checker, compiler, tests, formatter, toolchain/version lookup, environment/storage probe, Git operation, patch application, cache, scratch/temp/worktree or descendant was used. Actual Lean versions, theorem printed types, goals/diagnostics, kernel results and ALL complete axiom lists: **UNKNOWN / NOT RUN**. No checker receipt is inferred from source syntax or earlier receipts.

Verification handoff, only under a new primary-authorized execution envelope and verification-owner cache lease: build `YulangClosure.PermissionMemberWitnessR119` with pinned imports; run the proof skill's `check_lean.py --module YulangClosure.PermissionMemberWitnessR119` with all six fully qualified theorem names above as repeated `--theorem` arguments; inspect every printed type and complete #print axioms output, then repair from actual diagnostics. No root import was edited.

Only the two leased outputs were written. No generated outputs or scratch paths exist from this assignment. Artifact and this revision are frozen; handoff hash is reported externally to avoid a self-hash cycle. Writes STOPPED; no descendants or pending processes. Resource use beyond the fixed 300-second grant is UNKNOWN, not reclaimed as measured spare time. Return to primary for fresh independent review and research-artifact adjudication only.
