# R128 immutable Rust attachment audit — revision 1

Sprint `PERMISSION-BORROW-FOUNDATION/20261102-R128`; assignment `R128-SOURCE-1`, worker `/root/r128_rust_source`, sole author, no descendants. Outcome class: **source/native evidence and conditional paper derivation**. Independent review PENDING; no self-review claimed. Sole changed/leased path is this handoff. The primary assignment is the launch/activity receipt; observed model/effort are UNKNOWN.

## Baseline, authority and authentication

R128 contract SHA-256 `4f4c71e44ce17a8123a0d4f8bbc4f3e10f253e64d4d3fa0411b4c3059afff451`; manifest SHA-256 `3d067a53f428f18d33b291313e7db6a654ae70271f29af51921cf339d39eb827`. Research baseline `3f90fa0b741e1365afb3a4108184cec6f487d4da`; immutable Rust baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Every non-commit input in the R128 manifest was freshly hashed and matched. Receiver/effect/scheme Git blobs also matched their manifest hashes. No dirty/quarantined Rust file was opened.

Governing sections: R128 Outcome, Required Lean construction, Continuing lanes and exact leases, Success/blockers; `rules/research-lab.pre-sprint.md` One semantic baseline and Evidence quality; `rules/design-authority.md` Authority order and proof-obligation economy; `rules/git-concurrency.md` Integration ownership and Disjoint-file mode. Root AGENTS/base, current-state handoff protocol, and top-level inference principles §§1.1,3 were read. Accepted source scope, original A/B quantifiers, contravariant permission/open inflow and production gates are unchanged. This audit neither selects semantics nor constructs the principal theorem.

The R111 handoff freshly matched `54a79a1b4f49d75b78bd3c3e96ff2c317941c57e24dfbad6e2c441309f131d9d`. Its four receiver replacements were applied in memory with one occurrence per old pattern, reproducing `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`. Then R117 patch `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1` and corrected R119 patch `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a` were parsed and composed. Every hunk's old/new payload counts matched its header; each complete old payload had one exact match after the preceding consumed region. Relocation by full context was allowed, fuzz/context deletion was not. Untouched bytes and line endings were preserved.

The resulting receiver is exactly R127's `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`, 296,602 bytes, 5,872 lines. All receiver line numbers below refer to this virtual target, never a working-tree file. R111 adds only an import to effect, so its constructor/borrow bodies below are unchanged; effect line numbers refer to d177 before that one-line import. The R127/R120/R121/R119 handoffs were read as frozen evidence; their source-to-Lean gap verdict is preserved.

Additional exact identity dependency discovered through immutable `git grep` and `git show`: `d177:crates/yu-hir/src/module/source_annotation.rs`, SHA-256 `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`. This is a commit-pinned dependency, not a new source choice. Its hash is proposed for the primary's shared manifest; no shared file was edited.

## Complete family equality

Pinned `source_annotation.rs:32–36` defines precisely:

```rust
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceEffectId {
    pub module: Arc<ModuleId>,
    pub declaration: SourceNodeKey,
}
```

Thus `a == b` requires both `a.module == b.module` and `a.declaration == b.declaration` using those types' equality. Arc equality compares its inner value; allocation identity is not required. The identity has no spelling, range, visibility, operation member or type-argument field. `SourceOperationId` separately contains `family: SourceEffectId` and operation `declaration: SourceNodeKey`, also deriving Eq/PartialEq. Equal complete operation IDs imply equal complete family IDs; equal families alone do not imply equal operation declarations.

Every relevant predicate preserves both family fields: native allowed-member comparison at receiver 5141–5142, the operation-ID chain at 5151–5154, schema-family search at 5175–5177, selected-arm family comparison at 5178, actual provider-family search at 5184–5185, consumer option/reference equality at 1885–1887, provider operation family comparison at 1891, and allowed-member equality at 1898–1899. References are compared by their referenced values in these predicates. None reduces equality to declaration alone, Arc address, spelling or an integer coordinate. The record pointer guard at 1878 is a separate predicate and establishes no family-value equality by itself.

## Actual constructor, borrow and transport

Effect `candidate_formal_entry_annotation:1762–1834` reads annotation effects and registration, validates computation role, source owner/scope, recipe, exact owner-local Lambda/formal, and absent formal-domain/registration. For a nonempty concrete row it executes `concrete.extend(row.concrete.iter().cloned())` at 1790 and stores the complete ordered vector with exact registration/source fields at 1791–1802. After the optional symbolic equality succeeds it pushes the prepared record at 1818–1821. Order, duplicates, both family identity fields and length survive the copy under ordinary Clone/Vec meanings. Empty concrete rows create no retained record here; source admission remains broader. Allocation/identity/helper failures may prevent publication. POST storage does not establish the PRE-state Action/absence obligations.

Effect internal lookup 462–487 uniquely filters by registration, checks parameter/formal/owner/scope/occurrence/entry and nonempty concrete, then returns `InternalFormalEntryPermission { ... concrete: &permission.concrete }`. This is evidence of an actual full-vector shared borrow, including its length. The wrapper has borrowed fields and a slice; it is not a reference to the owning `FormalEntryPermission` struct itself.

Receiver capture validates owner/batch/live-state and incidence pointers, emission/admission identities, the selected native `AnnotationMember`, exact view pointer, closed operation-view tail, full allowed family, operation declaration Arc pointer and complete operation-ID chain. At 5158–5180 it selects exactly one retained permission by registration and checks all wrapper fields plus the concrete starting address. Then:

```rust
// virtual receiver 5182–5185
let provider_family = owner_view.allowed.get(member_index as usize)
    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
let permission_member_index = permission.concrete.iter()
    .position(|family| family == provider_family);
```

The projection stores `provider_family`, `permission_index: *permission_index`, `permission_member_index`, and `permission` at 5193–5196. Request construction copies those exact four fields at 4876–4879, alongside native view/member. At 4890 the inventory copier preserves `(packed index, borrowed permission reference)`; baseline helper 2258–2262 uses `items.iter().copied()`, collector 2242–2255 checks consecutive owner indices and pushes each item unchanged. It copies references, not permission payloads.

Consumer 1870–1875 independently demands a unique registration match. Its guard then checks packed index and record address, exact source fields, actual indexed family, native coordinates and complete operation/family fields:

```rust
if *permission_index != self.catch.permission_index
    || !std::ptr::eq(*permission, self.catch.permission)
    // intervening source-field comparisons, not elided executable rules
    || self.catch.permission_member_index
        .and_then(|index| self.catch.permission.concrete.get(index))
        != Some(self.catch.provider_family)
    // subsequent native and operation comparisons
{ return None; }
```

The comments abbreviate surrounding code only. If execution continues past the complete rejecting guard, short circuit evaluation implies the actual indexed expression was evaluated and equaled `Some(provider_family)`. Therefore some in-range index reads a complete equal family from this captured record's vector. This local implication does not need first-match history. Additional formal/recipe/route checks follow; passing this guard alone is not success of the entire function.

## Pointers and coordinates

Registration identifies a formal; packed permission index addresses its compact retained inventory; native view/member selects an allowed-family entry; concrete member index selects a position within the retained vector. The full family value is distinct from every coordinate. The record pointer is a sixth, physical observation. The vector's element starting address is a seventh observation; it is not the owning-record address.

At 1878 `std::ptr::eq` receives references to the sized `FormalEntryPermission`, implicitly converted to thin raw pointers. A true comparison establishes equal current addresses of these record referents. It does not compare payloads, registration, vector length/capacity/content, allocation history, provenance, or earlier/later heap states. Given valid live references in this path, it ties the inventory referent to the captured referent at this check. Temporal stability additionally depends on Rust validity/aliasing and the actual permitted execution.

At 5174 `permission.concrete.as_slice().as_ptr() != retained.concrete.as_ptr()` compares thin element pointers after slice metadata has been discarded. Equal start addresses do not establish equal slice lengths. Smallest useful nonempty paper witness: for one two-element array, full slice `&a[..2]` and prefix `&a[..1]` have equal `.as_ptr()` and unequal lengths. No dangling or unsafe value is needed. This refutes the stronger slice-equality inference only; it is not a reachable attack on the actual full-vector borrow above. In contrast, applying `std::ptr::eq` directly to two slice references compares their address AND length metadata. Actual code here does not do that.

Official Rust documentation consulted: [ptr::eq](https://doc.rust-lang.org/std/ptr/fn.eq.html), displayed Rust **1.99.1**, commit `58cf8f9c3`, dated 2026-10-13, documents address comparison and wide-pointer metadata; [Arc PartialEq](https://doc.rust-lang.org/std/sync/struct.Arc.html#impl-PartialEq-for-Arc%3CT,+A%3E), same displayed version, documents inner-value equality across distinct allocations. These docs support the operation meanings above; they are not an installed toolchain receipt or a formal source semantics. Version-specific 1.91.0 documentation fetches failed, so no 1.91 claim is made. Baseline R111 records no repository-pinned Rust toolchain.

## Exact remaining Rust-to-model equations

Let `D` decode a complete `SourceEffectId`, `V_t(p)` decode the ordered vector in live record/location `p`, `N` map valid usize values to Nat, and `H_t` interpret the actual heap. These are proposed relation names, not defined/established functions. Attachment still needs:

1. **Equality fidelity:** `D(a)=D(b) ↔ (a.module==b.module ∧ a.declaration==b.declaration)`; clone preserves D. A lossy family-number map cannot silently replace this premise.
2. **Construction:** successful actual publication associates one modeled location/record with the emitted Rust record, and `V_post(p)=map D(row.concrete)` preserving length/order/duplicates. PRE absence/source Action and symbolic-helper obligations remain separate.
3. **Borrow interpretation:** the returned slice denotes the entire same concrete vector, not merely an equal starting address; the actual retained reference has the modeled location/record identity. Source reference validity/lifetime/aliasing and mutation rules must simulate the model transitions. Deriving stability inside chosen model rules does not prove these source rules.
4. **Native selection:** successful indexed native view/member read decodes to the same full family D(f), with usize/index conversions faithful. Family identity follows from the complete operation comparisons, not coordinate coincidences.
5. **Search:** if actual `.position` returns `Some(k)`, `N(k)` is the least valid position j with `V_capture(p)[j]? = some D(f)`; `None` means no equal family. This needs iterator order, equality fidelity and overflow/index interpretation. Existing source capture guarantees existence via its earlier equal-schema-family search under ordinary semantics, but no Lean attachment proves that.
6. **Copy:** projection→request preserves `(p, optional k, f, packed index, native view/member)` exactly; borrowed inventory copying preserves record references and packed indices.
7. **Guard interpretation:** successful unique registration selection plus record pointer guard identifies the modeled selected record with captured `p`. Equal raw addresses alone cannot stand in for a cross-time identity theorem.
8. **Read:** if the actual Option/Vec guard continues, there exists k with actual optional index `Some(k)` and `V_consume(p)[N(k)]? = some D(f)`. A faithful same-record heap/vector read relation must establish this equation. For first-position preservation also use borrow stability and exact copy; membership only uses this read plus identity.

These premises are source-attachment obligations, not hypotheses already discharged by R128's independent Lean operational model. The original parent inference theorem, R39 PRE event, R45 extraction, full native decoding, source inference behavior and production remain OPEN. R111's capped verifier remains unmet; Cargo allowance is still 0/1.

## Coverage, resources and freeze

Inherited mandatory duplicate discriminator, not a new independent attack: `[9,9]` captures index 0 while local reads at 0 and 1 both equal 9. A changed index can satisfy the local guard without being the captured first index; no reachable tampering is claimed. None/out-of-range/missing-family/empty reads cannot equal `Some(f)`; duplicate registrations fail uniqueness; equal-payload records at different addresses fail the pointer guard. No additional executable mutation or search was run.

Oracle independence: byte composition/authentication was computed directly from Git blobs and full patch payloads, independently of narrative behavior claims. Behavioral derivations share ordinary Rust operation meanings and documented pointer/Arc semantics; there is no second independent executable semantic oracle. Seeds/ranges: not applicable, no enumeration. No Rust/Cargo/build/test/Lean/Lake, source materialization, environment/storage probe, generated cache, Git mutation, descendant or background process. Commands were `cat`, `rg`, immutable `git grep`/`git show`, `sha256sum`, inline single-process Python hash/composition/excerpt processing, official-doc web reads, and `apply_patch` only for this path. All final hash/composition assertions passed. Broad read output truncation was narrowed for the actual expressions. CPU/RSS/exact elapsed telemetry UNKNOWN; assignment hard bound 300 seconds; bounded source strings only, no heavy process.

Recommended next action: independent review should compare the frozen operational model with the eight attachment obligations above, explicitly rejecting any inference from model stability or pointer equality to an established Rust simulation.

**Writes STOPPED** at revision 1; no unresolved descendants. Freeze/hash returned externally. Commit packet: exact leased path `tasks/agent-loop/inbox/effect-permission-borrow-operational-foundation-r128-source.md`; baseline `3f90fa0b741e1365afb3a4108184cec6f487d4da`, source `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; no dependency hash changed, new discovered pinned dependency `source_annotation.rs` hash `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`; independent review PENDING; checks already run: manifest/file/blob hashes and exact in-memory R127 receiver reconstruction, static field/pointer derivation, official API-doc consultation. Proposed commit message: `research: pin permission borrow source attachment obligations`. Shared-record deltas intentionally left to primary/curator: add identity dependency pin, record complete two-field equality and eight residual equations, preserve all parent/production gates and R111 verifier status.
