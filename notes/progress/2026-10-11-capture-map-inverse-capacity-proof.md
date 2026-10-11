# Capture-map inverse: exact allocation branch

Date: 2026-10-11
Status: unreviewed constructive collection/source reduction; native all-history inverse premise OPEN. No constructor-qualified counterexample or W/A3 closure.
Producer: leaf `/root/retained_w_a3_rollback_proof`; no delegation.
Exclusive lease: this note only.
Baseline: `159ae453cd1ffc413180dcd5a308973089edb810`, branch `research/simple-sub-intrusion`.

## Frozen obligation and method

Resolve only the absent-key capture-bucket reinsertion premise identified by [the reviewed intrusion settlement audit](2026-10-11-intrusion-settlement-inverse-audit.md), “Exact stopping premise: capture-map reinsertion storage”. Governing authority is user-approved [suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §6: route mutation and failure restoration belong to one transaction, with required storage reserved before mutation. No semantic decision or supported source envelope changes.

For **every constructor-valid native route suffix** composed of capture admissions and splices, including later such mutations before failure, the required conclusion is that reversing its recorded bucket snapshots at `candidate_effect.rs:200–202` restores the exact pre-route map contents and each `insert(row, old_bucket)` completes allocation-free and normally. Source buckets, destinations, capture records, row identities and original snapshots remain distinct. Preserve the original parent's L/G/U, B/emission/raw endpoints/m/n, R/H/q/c, a=(R,i), F/j, finite ordered Q/A and `0≤d≤p≤|A|`, D/P/C and source binders; this local claim does not replace or close W/A3.

Method: pin the selected toolchain/stdlib dependency, derive its exact insertion/deletion credit transitions, then compose them with the two native map mutators and reverse snapshots. Do not assume either `try_reserve(1)` or a live len/capacity bound proves reverse headroom. The proof stops at a control-byte/source-history premise, not an arbitrary MAX state. This packet produced no execution probe or native counterexample.

Shared assumptions: ordinary valid owned collections, active matching route journal, constructor-valid acyclic record chains/indices, nonconcurrent session ownership, normal u32 hashing/equality and Copy bucket values. No user Hash/Eq/Drop callback is involved in this map. Exact content inversion of the saved bucket/link log is imported from the reviewed audit; other store/context/effect inverses and full rollback return are not assumed proved by this leaf.

## 1. Actual selected toolchain and source bridge

Read-only metadata `rustc -vV` reports Rust **1.95.0**, commit `59807616e1fa2540724bfbac14d7976d7e4a3860`, host `x86_64-unknown-linux-gnu`; `rustc --print sysroot` reports `/home/momota1029/.rustup/toolchains/stable-x86_64-unknown-linux-gnu`. `.cargo/config.toml` supplies only the xtask alias; no repository rust-toolchain file was found. These commands inspected metadata, not a compiler build or experiment.

The installed matching sysroot source's `std/src/collections/hash/map.rs` imports `hashbrown::hash_map` at line 4. Its `insert` delegates to `self.base.insert` (`1295–1296`); `try_reserve` similarly delegates (`903–904`). The sysroot `library/Cargo.lock:127–135` pins **hashbrown 0.16.1**, package checksum `841d1cc9bed7f9236f321df977030373f4a4163ae1a7dbfe1a51a2c1a51d9100`.

The local registry archive has that exact SHA-256. A read-only archive comparison established that the inspected map/raw/SSE2/generic source files equal their archived package contents byte-for-byte. Thus this is the exact registry dependency named by the installed std source, rather than another cached hashbrown version. The crate archive/source root is `~/.cargo/registry/{cache,src}/index.crates.io-1949cf8c6b5b557f/hashbrown-0.16.1` (cache suffix `.crate`).

This establishes the selected compiler/sysroot and its source dependency correspondence. No previously built solver executable or its linkage/build flags was inspected; an independently built binary using a different toolchain is outside that verified correspondence. The raw control-byte illustration below uses the selected x86_64 normal SSE2 group width 16 (`src/control/group/mod.rs:10–16`, `sse2.rs:27`). Different target/feature selection requires the corresponding group implementation.

## 2. Derive the actual insert/reserve condition

Write n for live items, g for `growth_left`, and c for `bucket_mask_to_capacity(bucket_mask)` in the actual allocated RawTable. Hashbrown's exposed capacity is **n+g** (`raw/mod.rs:1359`); it need not equal c because tombstones consume growth credit.

The call chain for this compiler field is:

```text
std HashMap::insert
  → hashbrown HashMap::insert                     map.rs:1841–1851
  → find_or_find_insert_index                    map.rs:1856–1868
  → RawTable::find_or_find_insert_index           raw/mod.rs:1161–1186
      reserve(1) BEFORE checking whether key exists
```

The unconditional reserve at `raw/mod.rs:1167` is decisive. It also occurs for replacement of an already present destination key. The distinct `RawTable::insert` optimization that first chooses a tombstone (`1074–1093`) is **not** the HashMap insert path used here; importing its behavior would give the wrong proof.

`reserve` (`955–969`) bypasses work exactly when g≥1. When g=0, it calls `reserve_rehash` with Infallible allocation behavior. `reserve_rehash_inner` (`2781–2830`) computes n+1 and:

- if `n+1≤c/2`, calls `rehash_in_place`, with no new backing allocation;
- otherwise calls `resize_inner` with requested capacity at least `max(n+1,c+1)`, which allocates a new table.

Thus, at each inverse HashMap insert, a sufficient and source-exact exclusion of the backing-allocation branch is

```text
g ≥ 1  OR  n+1 ≤ floor(c/2).                     (I)
```

Normal in-place rehash uses finite table operations and the ordinary u32 hasher; it restores g to c−n (`3020–3098`). No user destructor/hash callback supplies another failure here. The n+1 calculation is bounded by valid table capacity on these admitted branches. If g=0 and n+1>c/2, the allocation request really belongs to the source path; its success is not a theorem of reserved storage. Infallible allocation failure can abort rather than return the original route error.

Deleting a live key uses `RawTableInner::erase` (`3249–3307`). It marks the control byte EMPTY and increments g only when its adjacent EMPTY masks permit that marker. Otherwise it marks **DELETED** and leaves g unchanged. It always decrements n. Insertion of an absent key decrements g only when it consumes an EMPTY slot (`insert_tagged_at_index`/`record_item_insert_at`, `1210` onward, `2499`). These are concrete transitions of the actual library, not a supplied model.

Consequently neither a removal nor restoring the old live length supplies one reverse growth credit. A deleted slot available for the old key is insufficient too: this HashMap path reserves before looking for it.

## 3. Compose the actual native mutation suffix

The owning field is `candidate_effect::State::capture_incidence: HashMap<u32,CaptureBucket>` (`candidate_effect.rs:60`). Searches of its production references locate exactly the two forward mutators below and rollback. No forward shrink/replacement/clear of the entire map was found.

**Capture admission (`398–426`).** Duplicate `(source,view)` admission is read-only. Otherwise save the exact previous bucket at tail; reserve the undo, exact incidence key set, map and record Vec before publication. The map's successful `try_reserve(1)` establishes g≥1 immediately before its insertion. Updating an existing tail consumes no EMPTY slot. Adding a new tail can consume one, leaving g=0. Its reverse snapshot either inserts the saved old bucket or removes the newly created tail. The latter removal may create DELETED, hence may leave g=0 for the next inverse insert.

**Splice (`428–450`).** Equal row IDs or absent source return read-only. Otherwise the map reserves one credit, and undo records `(from,Some(source))` followed by `(to,destination)` before mutation. It then removes from and inserts the merged to. Let e_f be 1 when removal makes EMPTY, else 0; let e_t be 1 when an absent destination consumes EMPTY, else 0. Its postmutation credit is

```text
g_after = g_before + e_f − e_t,  where g_before≥1.
```

If destination exists, e_t=0 and this isolated forward step leaves at least one credit. If destination is absent, e_f=0 and e_t=1 are permitted by erase/insert behavior, leaving zero. Rollback reverses the destination snapshot first, then reinserts from. For a missing old destination it removes to, but that reverse deletion can also yield DELETED and return no credit. Therefore the source guard does not establish (I) at the subsequent from reinsertion.

**Later mutations and failed reservations.** Every later successful forward reserve proves a fresh local g≥1; a rehash/grow can change the map layout and thereby invalidate any proposed correspondence to the old slot. Forward admissions/splices log their exact logical bucket mutations; failures before publication add no new bucket log entry, although a successful earlier reserve may have changed layout. The reverse snapshot sequence restores logical keys/values, but does not restore control bytes or g. An induction on live keys alone cannot establish (I) at all reverse points. Subsequent reverse removes/replacements must be included in that proof.

This derives the needed history invariant precisely: **at every reversed Some snapshot, source history must establish (I) for the actual then-current control table**. A stronger adequate invariant is g≥the number of remaining inverse insert calls; no such invariant follows from the current single-credit forward guards, and this packet does not adopt it as a compiler restriction.

## 4. A concrete library branch, with its source gap explicit

The following uses real 32-bucket/SSE2 behavior, not a reduced machine word or scalar corruption. It shows why the simplest credit proof is unavailable. It is a conditional control-layout derivation, **not** a constructor-qualified Yulang counterexample.

Take c=28, n=27, g=1 and initially FULL controls at slots 0…26, EMPTY at 27…31, no tombstones. A source bucket is at slot 8; an absent destination's probe selects EMPTY slot 27. This is a valid raw-table arrangement conditional on those u32 hashes/key placements.

1. Splice's try_reserve(1) does nothing (g=1).
2. Removing slot 8 marks DELETED: the preceding and following EMPTY masks yield a nonempty run of at least width 16. Thus n=26,g=1.
3. Inserting destination at slot 27 consumes EMPTY, giving n=27,g=0; controls 0…27 are now FULL or DELETED.
4. Reverse removes destination 27. Its preceding 16 controls are nonempty, so erase marks DELETED, giving n=26,g=0.
5. Reverse reinsertion of source calls reserve(1) **before** finding the source's tombstone. Since 27>28/2, it calls resize_inner and requests a larger allocation.

Each arithmetic/control step follows the actual code. What is **not established** is that the native capture constructors, their row-ID allocation/order and the actual RandomState hashes yield this placement (or another allocating placement) in a qualifying retained Local route before its real failing sample. Neither caller source nor a random-hash intuition proves that. Allocation success/failure and an actual parsed source route were not observed. Therefore this packet reports neither refutation of the all-native theorem nor a witness that the allocator aborts.

## Exact result, remaining owner and economy

Established source-linked reduction: the current single-credit pre-splice reserve is not itself a proof of allocation-free reversal; the exact library branch is governed by (I), and tombstones plus unconditional pre-lookup reservation are operationally relevant. Even replacement is not universally allocation-free in this installed HashMap path.

**Remaining premise:** derive (I) at every inverse insertion from the full native capture admission/splice history, including actual u32/hash layout and later reversed mutations, or exhibit a constructor-qualified route reaching its negation. Owner: the capture incidence construction/rollback seam (`candidate_effect.rs:398–450,197–204`) together with this pinned HashMap bridge. If the runtime may differ, establish the actual linked binary's source/feature correspondence too. No allocator success assumption can close the requested allocation-free theorem.

This is A rollback correctness/storage, rather than stronger optional semantics or a new relation reconstruction. The operation already owns exact bucket/link snapshots; the missing fact is storage needed by their inverse. Another live-length proof or another restatement of try_reserve(1) would leave it untouched. Primary should use this decisive library branch to assign source-qualified placement evidence or adjudicate a constructor-owned storage repair, without narrowing the original source envelope. Only the primary owns implementation authorization and independent review.

The result also means allocation-free HashMap replacement cannot be imported as a general runtime axiom in other inverse notes. The frozen [context transport note](2026-10-11-context-transport-rollback-proof.md) was not edited; its corresponding assumption requires separate primary/reviewer adjudication where headroom has not been derived. No unrelated map owner was investigated here.

## Frozen inputs, checks and resources

| Dependency | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| Reviewed settlement audit | `d986ed3c9f53f88bf55904eb09ee7fa0c2217f816ab0183efedba175179ea71d` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Installed std HashMap source | `809f1f8ee73d80b575c76865be9d2e5dc1f1f188d4db2d1180ab7769568a06fd` |
| Installed std library Cargo.lock | `24ee3436f747470180e01a14bb9dea54eba96be15f65ab0407922a7132de84b4` |
| hashbrown 0.16.1 archive | `841d1cc9bed7f9236f321df977030373f4a4163ae1a7dbfe1a51a2c1a51d9100` |
| hashbrown `src/raw/mod.rs` | `c24d6b9c8a9456505fa7a5b7c42b85468e6dd76bd49af54d17696c16dec4d2e8` |
| hashbrown `src/map.rs` | `2f42092439f327756317ea15a32983cfd29503add8a6ff9716b92e50c03dfd7b` |
| hashbrown SSE2 group | `833da90ab3fd72d306d5b999de96a4b6b52aa1a16ee7273c89bd12c9ead3bc45` |

Checks: plain HEAD/ref reads, narrow source/owner searches and source reads, selected rustc version/sysroot metadata, installed std lock/delegation bridge, SHA-256 hashes and a single read-only Python archive equality check, static control-byte/counter derivation, final leased-note whitespace/hash inspection. No program/compiler probe, allocator observation, Cargo/test/build, measurement, Git command/mutation, code/test/shared-record edit or delegation. The absent registry `.cargo-checksum.json` was replaced by exact archive checksum/content comparison. Earlier policy/skill/role reads from this continuing leaf remain applicable; no routing/config change was inferred.

One lightweight process at a time; no sustained computation or performance samples. Packet started 01:54:54 UTC and froze within ≤20 minutes; CPU/RSS unmeasured. Requested normal prover Sol/high; actual role/model/effort metadata unknown. No Astra. Primary owns all executable verification and fresh independent review. Full W/A3 remains OPEN.

One next action: primary assigns the exact native placement/history question exposed by (I), or the corresponding source-owned storage gate, using this pinned library behavior.

## Commit packet

- Exact changed lease: `notes/progress/2026-10-11-capture-map-inverse-capacity-proof.md` only.
- Baseline: `159ae453cd1ffc413180dcd5a308973089edb810`.
- Changed dependency hashes: none authored; frozen inputs above match assigned compiler hashes.
- Review status: unreviewed constructive source/library reduction; native allocation-free inverse and W/A3 OPEN; conditional layout branch is not an authentic source counterexample.
- Checks run: static reads/searches, metadata, archive/source hashes/equality, control-credit derivation and note inspection; no executable verification.
- Proposed checkpoint message: `research: isolate capture rollback HashMap allocation branch`.
- Shared-record delta left to primary/curator: record exact condition (I) and unconditional pre-lookup reserve; keep native capture inverse OPEN and adjudicate imported replacement assumptions. No shared record or prior note edited.

Frozen after final checks; no further writes planned.
