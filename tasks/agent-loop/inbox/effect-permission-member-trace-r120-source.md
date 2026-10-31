# R120 source trace — frozen, static correspondence only

Assignment `/root/r120_source_trace`, sole leased output this file. Baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Method: authenticate immutable blobs and frozen artifacts, compose the two patches in memory, then inspect actual composed expressions. No compiler, Rust/Lean execution, test, filesystem patch application, synthesized source file, temporary file, environment/storage probe, Git mutation or descendant. Independent review pending. This is source evidence, not a proved Rust operational semantics or Lean correspondence.

## Exact composition

Freshly read receiver and effect blobs only through `git show <baseline>:<path>`:

| Input/result | SHA-256 |
| --- | --- |
| Baseline receiver, 292001 bytes | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |
| Baseline effect | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` |
| R117 revision-2 patch | `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` |
| Receiver after R117, 296297 bytes, 5864 lines | `542deb29c1143fad9adca958c3fadfa976e4505acc6f91dcf119ff0628f07e31` |
| R119 corrected patch | `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a` |
| Receiver after R117 then R119, 296776 bytes, 5875 lines | `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` |

Read-only Python byte/text processing decoded UTF-8, split lines retaining line terminators, parsed unified-diff hunks, asserted actual old/new payload counts against headers, and searched for the **entire exact old hunk payload** in the current input after the prior consumed region. Each hunk had exactly one match in that remaining input; no context line was dropped and no fuzzy match was used. Output concatenates untouched input segments and exact new payloads, preserving all line terminators, then encodes UTF-8 and hashes bytes. Each patch is applied to the previous in-memory result. No composed bytes were saved.

Line hints are not exact throughout. This algorithm explicitly permits relocation by unique full context; it does not establish zero-offset application by an external patch tool. Hunk order/counts and actual old/new starting lines (1-based in each patch's input/output) are:

| Patch/hunk | Header old start | Actual old start | Actual new start | Old/new count |
| --- | --- | --- | --- | --- |
| R117/1 | 231 | 231 | 231 | 4/8 |
| R117/2 | 603 | 603 | 607 | 7/11 |
| R117/3 | 1860 | 1860 | 1868 | 12/32 |
| R117/4 | 4844 | 4844 | 4872 | 3/7 |
| R117/5 | 5052 | 5052 | 5084 | 4/10 |
| R117/6 | 5106 | 5109 | 5147 | 12/43 |
| R119/1 | 237 | 234 | 234 | 5/6 |
| R119/2 | 610 | 611 | 612 | 4/5 |
| R119/3 | 1878 | 1879 | 1881 | 7/9 |
| R119/4 | 4880 | 4875 | 4879 | 4/5 |
| R119/5 | 5145 | 5168 | 5173 | 13/19 |
| R119/6 | 5158 | 5182 | 5193 | 8/8 |

All actual ranges are ordered and nonoverlapping. No hunk/context failure occurred under this stated method. A strict interpretation requiring advertised old positions without relocation would first fail at R117 hunk 6; do not silently identify that stronger claim with this composition.

## Source-owned chain

Numbers below refer to final composed receiver unless marked baseline effect. They identify the hashed virtual file above, not the dirty working-tree source.

Baseline effect `FormalEntryPermission`, 274–285, owns `registration: usize`, source/formal/scope/annotation fields, `entry_effect: u32`, and `concrete: Vec<SourceEffectId>`. Constructor `candidate_formal_entry_annotation`, 1762–1834, obtains the actual annotation row and formal registration; checks computation role, source owner, scope, recipe, owner-local lambda/formal, and absence of an existing formal domain or registration. Its exact order-preserving copy/publication expressions are:

```rust
// baseline effect 1786–1791
if !row.concrete.is_empty() {
    let mut concrete = Vec::new();
    concrete.try_reserve_exact(row.concrete.len()).map_err(|_| exhausted())?;
    temporary_bytes = bytes::<SourceEffectId>(concrete.capacity())?;
    concrete.extend(row.concrete.iter().cloned());
    let permission = FormalEntryPermission {
// 1792–1802 stores registration and exact source/formal fields, then concrete
// 1818–1821, after optional variable equality succeeds
if let Some((permission, retained_bytes)) = prepared.take() {
    let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
    state.formal_entry_permission_bytes = state.formal_entry_permission_bytes.checked_add(retained_bytes).ok_or_else(exhausted)?;
    state.formal_entry_permissions.push(permission);
}
```

This source copy retains order and duplicates. Empty concrete rows create no retained permission here; that is not rejection of source admission. Failed checks/allocation/equality can prevent publication. This excerpt does not authenticate the earlier source Action or reconstruct R39 PRE Inputs.

Baseline effect 462–487 selects exactly one permission by its `registration`, checks formal fields and nonempty concrete, and constructs `InternalFormalEntryPermission` with `concrete: &permission.concrete` and borrowed source fields. This is an actual borrow expression. It is not a theorem that an arbitrary wrapper with equal fields denotes the same allocation.

`ProviderNativeContextProjection::capture`, receiver 5080–5207, gets the owner source/internal projection, provider certificate and graph. At 5092–5096 it checks exact owner, batch and live-state pointers. At 5104–5116 it checks owner-local view inventory and internal incidence/emission/admission identities. At 5135–5147 the native endpoint must be `AnnotationMember(view_index, member_index)`, the indexed view must be the provider operation view by pointer, its tail must be closed, and its allowed member must equal `owner.schema.operation.id.family`. At 5152–5159 it joins declaration/provider/operation/selected-arm full identities.

At 5161–5183 the registration-keyed retained lookup is unique and field/slice-pointer checks remain explicit:

```rust
let retained = &source_internal.internal_incidence.permission;
let mut matching_permissions = source_internal.formal_entry_permissions.iter().filter(|(_, permission)| {
    permission.registration == retained.registration
});
let Some((permission_index, permission)) = matching_permissions.next() else {
    return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
};
// rejects a second match; compares parameter/formal/occurrence/owner/scope/
// annotation/source-row/entry fields, including:
// permission.concrete.as_slice().as_ptr() != retained.concrete.as_ptr()
// permission.concrete.iter()
//   .position(|family| family == &owner.schema.provider_identity.family).is_none()
```

The pointer comparison here compares starting addresses; it does not itself compare slice lengths or certify an arbitrary slice's provenance. The baseline borrow construction supplies concrete source evidence for the intended slice. No Lean pointer/slice interpretation is present in the authorized modules.

The actual witness construction at 5185–5199 is:

```rust
let provider_family = owner_view.allowed.get(member_index as usize)
    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
let permission_member_index = permission.concrete.iter()
    .position(|family| family == provider_family);
let result = Self {
    source_internal, provider, views,
    catch_fact_owner: ProviderFactOwner::BatchOccurrence(catch_fact_index),
    provider_view_index: view_index as usize,
    provider_member_index: member_index as usize,
    provider_family,
    permission_index: *permission_index,
    permission_member_index,
    permission,
};
```

Projection fields at 225–239 carry both `permission_member_index: Option<usize>` and `permission: &'a FormalEntryPermission`. `InventoryPackage::capture` obtains that provider projection (baseline function 4613; final function shifted by preceding hunks), builds `InventoryCatchRequest` at 4871–4887, and copies the exact fields:

```rust
provider_member_index: provider.provider_member_index,
provider_family: provider.provider_family,
permission_index: provider.permission_index,
permission_member_index: provider.permission_member_index,
permission: provider.permission,
```

At 4893 the permission inventory is copied with `copy_owned_borrowed_inventory(&source.formal_entry_permissions)?`. Baseline helper 2258–2262 uses `items.iter().copied()`; baseline collector 2242–2255 preserves each reference and checks sequential owner indices before `inventory.push((owner_index, item))`. It copies inventory entries, not permission payloads. Package assembly stores this local `catch` at 5069 and calls `package.internal_root_view()?` at 5073.

`internal_root_view` delegates to `internal_root_view_from`; consumer 1870–1901 uniquely selects `self.permissions` by `request.registration`, then checks:

```rust
if *permission_index != self.catch.permission_index
    || !std::ptr::eq(*permission, self.catch.permission)
    // source/registration/row/entry checks
    || self.catch.permission_member_index
        .and_then(|index| self.catch.permission.concrete.get(index))
        != Some(self.catch.provider_family)
    // native view/member, full operation and allowed-family checks
{
    return None;
}
```

Thus exact reference transport and the same-record indexed read are textually visible: the search uses `permission.concrete`; that `permission` reference and search result populate projection fields; request fields copy both; consumer uses `self.catch.permission.concrete` and its copied index. Its separate pointer check binds inventory lookup to that captured record. This chain does not infer pointer identity from value equality. Under ordinary safe Rust immutable-borrow semantics, these expressions preserve the borrowed record/vector; Rust compilation, borrow checking, executable reachability and formal operational interpretation are unverified here.

## Coordinates and falsifiers

Five independent coordinates are retained: formal `registration`; packed permission inventory `permission_index`; native `provider_view_index`/`provider_member_index`; concrete `permission_member_index`; resolved `SourceEffectId` family value. No numeric coincidence establishes identity.

These are static discriminating cases, not executed tests or authenticated source programs:

- Earlier unannotated formal plus later registration 7: the unannotated/empty concrete constructor creates no permission; a later nonempty registration can occupy packed slot 0. Lookup filters `.registration == 7` and transports packed 0 separately. Whether that whole source program reaches this package requires other owner/source obligations; this note does not invent that execution.
- `[4,9,9]` with provider family 9: first matching concrete position is 1; native member 0 may also name 9. A consumer index changed to 0 reads 4 and rejects. Changing it to 2 still reads 9 and passes this local member guard, so the guard alone does **not** establish first-match identity. The direct field transport supplies the source-level reason the unmodified path retains 1.
- Empty vector: constructor does not retain it, internal permission lookup rejects it, and capture's first search rejects it. Hypothetical forged empty records therefore are not ordinary successful capture results.
- Missing provider family: capture rejects when the schema-family search is absent. Successful prior view/full-identity checks equate schema family and `provider_family`; therefore the later optional search is also for that family under ordinary equality semantics. An absent later index is represented in the field type but is not a demonstrated reachable successful capture. A forged `None` or out-of-range `Some` rejects at consumption.
- Duplicate registration: capture and consumer both reject a second matching record. Equal family duplicates do not imply duplicate registration and are retained.
- Different record with identical value: the consumer's `std::ptr::eq` rejects a different record address even if registration/family payloads coincide. A pointer-equal record with a tampered index may still pass if the new index holds an equal duplicate, as above. No pointer semantics are modeled in R119 Lean.
- Foreign owner/batch/live state: the explicit capture pointer guards reject a mismatch before the witness is built. This is a source guard observation; no forged Rust object or whole-language counterexample was executed.

## Claim and exact obstruction

**Authenticated source bytes and textual field-flow trace obtained; `NO_AUTHENTICATED_TRACE` for the requested Rust-to-Lean operational relation.** R119 `orderedSearch` explicitly calls itself a candidate transcription of `iter().position`. The authorized Lean module has finite lists/values and no Rust iterator state, heap/vector/slice relation, lifetime/borrow semantics, `usize` interpretation or pointer relation. There is no already established theorem deriving `orderedSearch decodedConcrete family = some member` from this actual Rust search, nor deriving Lean indexed-read equations from Rust `.get` on the authenticated borrowed record. Choosing equal-looking Lean lists cannot establish these missing premises. No new semantics, faithful-decoder law or model was introduced. R118/R119 finite lemmas remain conditional/unchecked; R39 PRE construction, R45 extraction, R114 transport, parent soundness/effect hygiene and production stay OPEN.

Oracle independence: the composition calculation used exact baseline bytes and exact diff payloads, independently of authors' behavior descriptions; hashes and full-context uniqueness identify the source. The behavioral analysis uses those resulting expressions and ordinary library/borrow meanings, not a second implemented oracle. No behavioral execution, exhaustive state range, seed, mutation run, kernel receipt or Rust standard-library formal semantics was observed. Cases above are paper falsifiers of individual guards and stronger claims. They do not prove all reachable owner states or all source programs.

## Frozen dependencies, commands, resources and commit packet

Fresh SHA-256 authentication also matched: R117 handoff `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`; R117 review2 `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`; R119 handoff `731cc66eacc5f271bdf1d70054b8430ac0641ac55ac07281123f9fe5645e8e98`; R119 review `e4b9a3bf3d6b28ef2d1b5d77bbbc6345826f1a96d868efe10994dfac83fb230b`; R119 Lean `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`; R119 proof `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d`; R118 `NativePermissionDecoderR118.lean` `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`; R118 proof `fa4fcadbf028846469897aa815df4f58a9daeff58740f04891efde651edf6e79`; R118 review `bee20cccf34f82388f5f68836e95865c1f878381c45f0fa7df7a95cce8d0ef7b`. No dependency changed. One attempted locator `PermissionDecoderR118.lean` was nonexistent; corrected to the actual import `NativePermissionDecoderR118.lean` and authenticated its pinned hash. This was a locator error, not a Lean failure.

Commands: read-only `cat`, `rg --files`, `git show` and inline Python SHA-256/hunk composition/excerpt extraction; `apply_patch` only writes this leased handoff. Composition/count assertions and hash reads succeeded. No Rust/Lean/checker/test/build execution. Wall cap 300 seconds; CPU/RSS and exact elapsed telemetry UNKNOWN (not instrumented); only small source byte arrays were held in process memory. No resource probes. Writes STOPPED after this artifact; no child or background process.

Recommended next action: the assigned Lean lane should inspect these exact source expressions against existing R119 definitions and identify the first absent operational relation without filling it with a new assumed semantics; independent review should recompute the composition hash and challenge duplicate-index and slice-pointer claims.

Commit packet: exact path `tasks/agent-loop/inbox/effect-permission-member-trace-r120-source.md`; baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; unchanged dependency hashes above; independent review PENDING; proposed message `research: authenticate composed permission member source trace`; shared-record delta for primary only: record exact final virtual receiver hash, unique-context relocation method, visible same-reference transport, and missing Rust-to-Lean operational interpretation. No source integration or theorem closure.
