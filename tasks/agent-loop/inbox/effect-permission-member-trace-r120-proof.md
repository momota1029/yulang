# R120 Lean trace handoff — revision 1

Outcome: **`NO_AUTHENTICATED_TRACE`**. The frozen Rust source trace exposes direct index/reference field transport. None of the authorized existing Lean declarations derives its search, transport or indexed-read equations from that Rust execution. No new theorem, semantics, model, assumption or Lean module was introduced. This is a static source/native gap analysis; independent review is PENDING.

Sprint `EFFECT-PERMISSION-MEMBER-TRACE/20261102-R120`; contract SHA-256 `85246d529c175e7a2c765d575d500948d34e05d44647aa8309cdebe49484c2dc`. Assignment `/root/r120_proof_trace`, registered Lean leaf; launch/resume authority is the primary's exact packet and current-session worker/lease entry. Sole author; no descendants. Requested and observed model/effort UNKNOWN. Exact sole write lease: this handoff. Other workers' files and dirty/quarantined Rust were not inspected or changed.

## Original authority, parent and frozen inputs

Read root AGENTS and its preserved base, goal-driven sprint rules, the proof skill and its `references/sources.md` and `references/execution.md`, handoff protocol, current exact assignment, and the R120 contract. The contract explicitly forbids Lean/Lake/checker execution and new modules; it controls over the skill's usual execution workflow.

Authoritative policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, SHA `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §1.1, SHA `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`. Contravariant permission, actual inflow and residual remain distinct. An annotation `[signal]` admits otherwise compatible `[signal,write]` input, permits handling signal, and preserves outward write. No restriction to closed input or singleton inflow is introduced.

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`, SHA `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This is a proposition definition, not an established concrete instance. `docs/yulang-whole-proof-closure-ja.md` §§1,3–4, SHA `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`, preserves full accepted source scope and the same lexical scope/shared witness. Its opening birth-level SCC correction remains in force. The operational integration draft supplies no new semantic authority.

The following hashes were freshly recomputed with `sha256sum` and matched their pins:

| Input | SHA-256 |
| --- | --- |
| Frozen R120 source handoff | `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e` |
| R119 `PermissionMemberWitnessR119.lean` | `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f` |
| R119 proof handoff | `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d` |
| R118 `NativePermissionDecoderR118.lean` | `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` |
| R39 `ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R45 `InternalPermissionIncidenceR45.lean` | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| R116 `SuppressionPermissionR116.lean` | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |

Rust context is exclusively the frozen source handoff. Its baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, patch identities and final virtual receiver SHA `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` are inherited source-lane evidence, not independently recomputed composition by this Lean worker. No Git blob or working-tree Rust was read here.

## What the existing Lean statements actually supply

All names in this paragraph have prefix `YulangClosure.PermissionMemberWitnessR119.`. These are **written source types**, not printed checker results; R119 remains CONSTRUCTED / UNCHECKED.

1. `search_index_read (xs : List Id) (family : Id) (member : Nat)` assumes `orderedSearch xs family = some member` and concludes `xs[member]? = some family`.
2. `indexed_read_member (xs : List Id) (member : Nat) (family : Id)` assumes `xs[member]? = some family` and concludes `family ∈ xs`.
3. `same_record_search_read (permission : ComputationPermissionEntryR39.Permission Id) (searchedFamily consumedFamily : Id) (permissionMember : Nat)` assumes both `orderedSearch permission.concrete searchedFamily = some permissionMember` and `permission.concrete[permissionMember]? = some consumedFamily`; it concludes `consumedFamily = searchedFamily ∧ searchedFamily ∈ permission.concrete`.
4. `selected_retained_member` adds arbitrary native-view and permission lists, endpoint, separate registration/storage coordinates, and successful `NativePermissionDecoderR118.readFamily`/`readPermission` equations. It retains the same `searched` and `consumerRead` premises. It concludes the exact native list reads, singleton registration-filtered selection, consumed/provider equality and membership. It does not derive any premise from Rust.
5. `certificate_member_if_extracted` assumes `InternalPermissionIncidenceR45.extract e q probe = some out` and search/read equations on **probe.permission at the same index**; it concludes provider-family membership in `out.permission.concrete`. It uses R45 `accepted_payload`, whose own type retains the explicit successful-extraction premise.
6. `distinct_coordinates_and_duplicates` states a finite example: registration 7 at packed slot 0, concrete `[4,9,9]`, search index 1, native view/member 0 reading 9, and selected coordinate inequalities. Its `by decide` has not run. No source program/reachability statement occurs in its type.

`Id` remains arbitrary with `DecidableEq Id`; lists retain order and duplicates. R39 `Permission` contains values and `concrete : List Id`; it contains no allocation identity or Rust reference. R118 `Endpoint` has only `view/member : Nat`; its `readFamily`, `matching` and `readPermission` are finite list functions. Its older `decode` still uses the R118 `contains` guard and has no R119 projection/request index field. Thus that function cannot serve as an operational trace of the updated R119 path. No existing declaration here quantifies over a Rust heap, iterator state, borrow, slice, `Option<usize>` field or execution relation.

## First missing relation and exact source trace boundary

The source handoff identifies final virtual receiver 5185–5199: obtain `provider_family`, evaluate `permission.concrete.iter().position(|family| family == provider_family)`, and store that result together with `permission` in `ProviderNativeContextProjection`. At 4871–4887 the request copies `provider.permission_member_index` and `provider.permission`. At 1870–1901 the consumer uses `self.catch.permission_member_index.and_then(|index| self.catch.permission.concrete.get(index))`; a separate `std::ptr::eq` compares the selected inventory permission to the captured permission. This is useful textual evidence for the intended source path.

The **first unavailable application premise** of R119 `search_index_read`/`same_record_search_read` is:

```lean
orderedSearch permission.concrete providerFamily = some permissionMember
```

with `permission`, `providerFamily` and `permissionMember` interpreting **those actual Rust values**. There is no authorized operation/representation relation from the concrete Rust vector and resolved `SourceEffectId` equality, iterator traversal and returned `Option<usize>` to R119's list, `DecidableEq Id`, `Option Nat` and `orderedSearch`. The search equation is an input of the existing theorem; no preceding theorem constructs it from the Rust expression. Choosing a list and declaring its elements to be decoded Rust values would add an unproved premise.

The later missing links are also independent: exact copying of the optional index and borrowed record through projection/request; conversion of the actual successful `.get(index)`/comparison into `permission.concrete[permissionMember]? = some consumedFamily`; and preservation/authentication of the same borrowed record/vector, state and batch. Those fields/references have no existing Lean trace representation. Equal list/record values cannot establish physical pointer identity. Conversely a source pointer check alone is not a Lean borrow theorem. The source handoff correctly notes that the capture's slice starting-address comparison does not by itself compare slice lengths; the baseline borrow construction is additional source evidence, still uninterpreted here.

Therefore the exact trace cannot be derived within this packet. This finding does not refute the intended safe Rust behavior, and it does not substitute an assumed faithful-decoder law for the missing evidence.

## Falsifiers and scope

These are symbolic consequences of the displayed definitions/guards, not executed Lean or Rust tests:

- For `[4,9,9]` and family 9, `orderedSearch` returns `some 1`. Reads at both 1 and 2 yield 9. Changing a captured index from 1 to 2 can pass the local Rust indexed-family guard while failing the stronger claim that the first-search index was transported. Applying `same_record_search_read` at 2 would require the false search equation `orderedSearch [4,9,9] 9 = some 2`; membership at 2 cannot supply it. The direct source field-copy expressions support the intended unmodified path, but are not formalized by R119. Changing to index 0 reads 4 and fails that local family guard.
- Empty and missing-family lists return `none` under `orderedSearch`; no successful search premise follows. The source constructor retains no empty-concrete permission, and capture rejects an absent family, according to the source handoff. A `None` or out-of-range index fails the consumer member guard. These hypothetical values are not demonstrated reachable successful captures, and empty annotations remain admitted source cases.
- Two distinct Rust permission records with equal field/list values can have one identical R39 `Permission` value; R119 cannot distinguish their physical identities. The source consumer's pointer guard distinguishes different addresses under ordinary Rust meaning. This is a representation gap, not an executed foreign-record counterexample.
- Duplicate family identities preserve their positions; duplicate registration records are a separate uniqueness failure. Formal registration 7 after an earlier unannotated formal can be distinct from packed slot 0, native endpoint member 0 and concrete member 1. R119's finite example preserves these coordinates but constructs no whole source execution.

No accepted constructor is removed. Polymorphism, symbolic effect variables, callback/computation annotations, open inflow, nested handlers and continuations stay in the original parent domain. Their generation/propagation/native behavior is not established by these local list facts.

## Parent application, owners and next boundary

No new premise for the original `InferenceSoundness` root or complete effect hygiene has been discharged. R116 `selected_endpoint_member` still needs the SAME R39 `prepare`/`permissionFor` equations, selected row, operation match and endpoint-family relation. R39 `Valid` explicitly requires that the action registration is absent from the PRE retained-registration list; the existing post-state decoder cannot reconstruct that absence. R45 `extract` still requires all `OwnerReads` and `Identity` conditions, not merely the membership conclusion. R114 transport, original source/native correspondence, parent soundness and production remain OPEN.

Mutual TODO `R119-AUTHENTICATE-MEMBER-TRACE-1` remains OPEN at the exact search-operation/representation relation above, owned by the native decoder/projection correspondence lane through the primary. Any next packet needs primary-authorized governing operational interpretation and exact leases; the present no-new-semantics/no-execution envelope ends here. Required evidence would justify this specific source search and transport, with duplicate-index 1→2 and different-record cases as discriminators, rather than postulate a generic faithful decoder. R39 PRE reconstruction remains separately owned by the source-constructor/proof lane; it is not merged into this TODO.

## Checks, resources and writes stopped

Actual commands: read-only `cat`, `sed`, `rg`, `sha256sum`, and one inline Python read/filter of current assignment state. All returned exit 0. Some batched read outputs were truncated; focused reads subsequently supplied the exact relevant definitions and source handoff. No mathematical or toolchain failure was observed because none was executed. The on-disk pin was read as `leanprover/lean4:v4.35.0`; project `-j1/-M1024` and empty external-package manifest were read. Actual executable versions, printed theorem types, goals, kernel results and complete `#print axioms` outputs for every R119 declaration are **UNKNOWN / NOT RUN**. Audit directives already written in R119 are future commands, not receipts.

No Lean/Lake/checker/compiler/build/test execution, tool lookup, environment/storage probe, cache, generated file, scratch/temp/worktree, patch application, Git mutation or descendant occurred. `apply_patch` wrote only this handoff. Bound ≤480 seconds; exact elapsed CPU/RSS telemetry UNKNOWN and no measured unused budget is claimed. No process remains from this assignment. Writes **STOPPED**; this revision is frozen and its hash is returned externally. Only this handoff is a proposed research checkpoint; independent review and integration remain primary-owned.
