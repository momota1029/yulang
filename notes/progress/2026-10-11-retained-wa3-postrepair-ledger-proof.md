# Retained W/A3: postrepair ledger derivation

Date: 2026-10-11
Status: independently reviewed conditional constructive derivation under the explicit Rust allocation model below. Actual linked-runtime applicability remains unverified; original W/A3 remains OPEN.
Producer: leaf `/root/retained_w_a3_rollback_proof`; no delegation.
Exclusive lease: this note only.
Baseline: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`, branch `research/simple-sub-intrusion`.

## Frozen objective, statement and authority

Apply the implemented `preflight_bound_capacity_growth` guard to the inequalities in [the reviewed headroom derivation](2026-10-11-retained-wa3-ledger-headroom-proof.md), then establish byte representability at the actual collection owners. Authority is [private candidate suspension](../design/2026-10-11-private-candidate-suspension-contract.md) §6, approved by the user with “承認して実装を進めて”. The primary reports that the guard repair has independent compiler-referee/spec-auditor review and focused passing tests; this leaf neither repeats nor substitutes those tests for the proof.

Preserve [the original composition](2026-10-11-nonterminal-drain-owner-composition-proof.md), “Frozen objects, statement and exclusions” and H1/W, and [the handoff derivation](2026-10-11-retained-parent-handoff-proof.md), A3/A4. Fix original L/G/U; B, accepted emission, raw endpoints, m/n; R, ordered finite H/q/c; a=(R,i), F/j; finite ordered Q/A and `0≤d≤p≤|A|`; diagnostic projection D, both processing scopes P and C. Keep source scopes/binders, occurrence/cause, context, fiber, attachment, provider, witness and residual lineage distinct. Equal endpoints or payloads do not merge occurrences. A history may start at any native retained cut, including Running or Ready; there is no fresh-call-only restriction.

**Narrow required conclusion:** for every constructor-valid retained Local history and every failed route, the actual late bound-ledger reconciliation, when entered, performs representable arithmetic and introduces no `accounting_error`. This is the accounting component of normal rollback return. It does not assert that preceding semantic inverses always reach it. The original parent's broader all-valid-initial-state/scheduler bridge, exact semantic inverse laws, incidence and lifecycle requirements remain unchanged and OPEN.

**Claim class:** a candidate constructive proof of this narrow operational conclusion under R below. No additional numeric source-envelope hypothesis is used. The proof does not assume prior rollback success. It derives the ledger/history invariant over failure transitions together with the forward transitions. Applicability of R to the actual linked compiler/runtime is explicitly unverified; the output is not an unconditional binary-runtime certification.

## Shared Rust allocation model R

R is the ordinary operational contract of the unqualified, nonzero-element `Vec<T>` used here:

1. Its reported capacity times element size is at most the size of its owned allocation; live nonzero allocations backing distinct owned mutable Vec buffers have disjoint, non-null byte addresses in one `usize` address space. Allocations do not wrap that address space.
2. `try_reserve(1)` leaves capacity unchanged when `len<capacity`; otherwise a capacity increase retains all old elements and does not shrink capacity. An ordinary reserve error leaves a valid Vec. `truncate` does not shrink capacity. A test wrapper can reject after successful allocation without invalidating that ownership.
3. The constructors and collections obey ordinary Rust ownership/validity; there is no forged Vec capacity, raw-buffer alias, arbitrary scalar overwrite, continuing execution after undefined behavior, or allocator implementation that violates its allocation contract.

These are runtime/library validity assumptions, not an assumption that accounting or rollback checks succeed. They impose no new limit on supported source, no requirement that allocations succeed, and no association between historical event counts and live bytes.

The installed library sources provide separate read-only grounding: unqualified Vec memory layout and guarantees (`alloc/src/vec/mod.rs:54–63,305–332,366–394`), RawVec's spare-capacity test and fallible growth (`alloc/src/raw_vec/mod.rs:501–535,679–696,764–766`), allocation address/nonwrap properties (`core/src/ptr/mod.rs:105–139`), and the allocation API (`core/src/alloc/global.rs:147–176`). These are snapshots under `stable-x86_64-unknown-linux-gnu`; this lane did not determine the actual rustc/stdlib binary linked by the primary. In particular, reading a local library source is not evidence that a different compiler binary implements it.

## Actual construction and consumption owners

Source locators below are in `crates/yu-solver/src/` at the baseline.

| Owner | Source fact used in the derivation |
| --- | --- |
| `lib.rs:734–769,3968–3990` | The four nested lanes of each value/effect row own Vecs of `u32`, `ValueEndpointKey` or `EffectEndpointKey`, all nonzero element types. The census enumerates row storage, not semantic witnesses or lineage. |
| `lib.rs:9775,10039–10083,10139–10204` | Payload initializes to zero; collected/parameter/fresh rows are `Default` with empty nested Vecs. New row construction changes outer storage, not the nested payload charge. |
| `lib.rs:9241–9336` | Pre-existing row snapshots precede their mutations and retain each lane's entry capacity once per route generation. New rows use the creation frontier. |
| `candidate_extrusion.rs:411–429,459–581` | All candidate insertion lanes call the guard, reserve one element, account actual capacities, then push. Intrusion transfers append to physical destination storage while retaining source storage (`candidate_intrusion.rs:546–595`). |
| `lib.rs:11694–11728,11771–11788,11829–11846,13751–13785,13839–13856,13917–13934` | Ordinary value/effect nested reserves use the same guard. Paired direct edges check again immediately before the second reserve, after accounting the first. |
| `lib.rs:14114–14147` | Full Vecs preflight current growth/rebuild counters, journal E+1/T+1, and incoming checkpoint counters plus E+1. Spare-capacity paths return without a count restriction. |
| `lib.rs:14150–14202,14260–14370` | Actual capacity changes increment E; successful record increments current growth/rebuild, T for old rows, and actual nested bytes. Immediate error propagation prevents a second unrecorded growth after a failed accounting call. |
| `lib.rs:9430–9482,9514–9641` | Rollback truncates row contents/new rows, resets entry payload/counters, reconciles surviving lane deltas, then history counts. Capacity is not shrunk for old rows. |
| `lib.rs:9666–9700` | The accumulated accounting result is returned after workspace reversal. No late arithmetic error is silently converted to successful rollback. |

Bound-table field/mutation and counter-writer searches found no production nested-capacity mutation outside these reserve owners, row construction, and rollback truncation in the inspected call cone. Direct test reserves/scalar assignments are not constructor transitions. The fixed retained Local owner is `candidate_scheme.rs:1466–1500`; its normal invocation uses nonincoming accounting, but its session may inherit incoming histories from synchronous Local routing (`1358–1407`). Both branches are therefore retained in the proof.

## 1. Derive the byte bound from ownership

Let M=`usize::MAX`. For each currently owned nested lane s, write capacity c_s and element size w_s as mathematical integers. Source field ownership gives one buffer per lane; source enumeration visits it once. Zero-capacity buffers charge zero and need no distinct address. For positive capacity, R gives an owned backing range of at least `c_s w_s` distinct byte addresses. These ranges are disjoint across the enumerated buffers.

Injection of all charged bytes into the finite non-null address set therefore gives

```text
L = Σ_s c_s w_s ≤ M.
```

This proves each multiplication and every nonnegative prefix sum representable. Extra allocator slack, outer row storage, unrelated memos, undo and other session allocations can only reduce the address space available to these buffers; they are not added a second time to L. No HashMap capacity formula or assumption about identical buckets is needed.

The unchecked `reconciled_bound_growths += 1` is representable too. If N value/effect rows survive, K≤4N. Each corresponding outer row element contains four nonzero Vec fields, so its byte size is at least four; the owned outer Vec backing covers at least N such elements. R bounds that backing charge by M, hence `4N≤M` and K≤M. This is a bound on the current enumeration count, not a bound on historical growth counters.

## 2. Derive the exact payload invariant, including failures

Use induction on the actual constructor and route transitions. At initial session construction, the nested lanes are empty and `bound_payload_bytes=0=L`. Appending a default row preserves this equality. Every physical nested growth is at an inventoried owner and accounts its actual capacity delta before any logical push; pushes within reserved capacity do not change L.

Before a growth let payload be the exact old L, and let capacities change x→y in one lane. Monotonicity gives `δ=(y−x)w≥0`. The current physical charge is `L+δ≤M` by section 1, so the multiplication, payload increment and independent lane increment are representable. Under the new guard, the count checks also succeed as proved next. Thus ordinary post-reserve accounting publishes the exact new L. A later diagnostic/resource sample error or post-reserve wrapper error cannot erase that accounting fact. A rejection before reserve changes no lane.

On rollback, let B be the saved exact entry payload. For each surviving lane let entry/current capacities be x_s/y_s. Once-per-row journaling and capacity monotonicity make its aggregate delta exactly `Δ_s=(y_s−x_s)w_s`. Rows created by the route are dropped before reconciliation. Unjournaled old rows did not change capacity. Therefore the physical charge after row truncation is exactly

```text
B + Σ_surviving_changed_lanes Δ_s = L_survivors ≤ M.
```

Resetting the ledger to B followed by the real reconciliation loop adds each of these deltas once. Each prefix is bounded by L_survivors. The independent test lane ledger has the same argument restricted to that lane family. Counter safety below makes each record publish, so the final payload again equals the actual physical census. This **proves** the equality needed for the next failed or successful route; prior rollback success was not an induction hypothesis hidden in the entry state.

The two normal early Result exits in outer rollback (`lib.rs:9377,9389`) precede nested-lane truncation and ledger reset. Their preceding graph/store inverse operations do not change these nested buffers or their payload field. Native forward accounting has already published L, so even such an early return preserves the current physical byte equality; this history induction does not need to assume those exits impossible. Once nested truncation begins, no further Result propagation precedes the reconciliation loop. A panic or invalid semantic inverse is not certified as a normally returning constructor transition. The native byte invariant does not manufacture successful preceding semantic inverses or the original C restoration.

For the supplementary test hook that rejects only forward byte preflight after a real reserve, the last delta may be temporarily unrecorded. The checkpoint B still describes entry storage, and the same survivor argument accounts that real delta if rollback reaches reconciliation; no MAX scalar assignment is needed or used. This supplementary statement does not claim a history invariant after combining an injected accounting rejection with an unproved early semantic exit. In native construction under R, the arithmetic argument above excludes that accounting rejection itself.

## 3. Apply the guard to both historical-counter branches

Keep the reviewed notation: entry growth/rebuild counts G/J; K changed surviving lanes; T successfully recorded old-row growth events; E recorded physical events; f successful records in this route. With no hidden commit/reset, current counters are G+f/J+f. The guard and reserve are consecutive synchronous operations on the same session; the wrapper cannot mutate those session counters between them.

When `len<capacity`, R says `try_reserve(1)` cannot change capacity, so bypassing the guard adds no event or rollback increment. When a reserve can change capacity, `len=capacity` and the guard establishes:

```text
G+f+1 ≤ M, J+f+1 ≤ M, E_before+1 ≤ M;
for an old row, T_before+1 ≤ M;
incoming additionally: G+E_before+1 ≤ M, J+E_before+1 ≤ M.
```

No allocation needing these facts occurs if the guard rejects. If allocation succeeds, at most one event is added. E's update cannot fail after an admitted guard, including a later rejected byte preflight. If accounting rejects, the owner immediately returns; there is at most one final unrecorded physical growth. If accounting succeeds, f and, for old rows, T advance once. The separately guarded second half of a paired edge reads those updated counts, so a first successful reserve is not mistaken for reservation of a second event.

**Nonincoming.** If no physical growth escaped successful recording, K≤T≤f. Checked forward records establish G+f/J+f≤M, hence both `G+max(T,K)` and `J+max(T,K)` fit. If a final admitted growth is unrecorded, K≤T+1≤f+1. That growth's pre-reserve guard established G+f+1/J+f+1≤M, so the same two inequalities still fit, even for a newly changed surviving lane. A failed guard adds no new K. This fills the exact one-event gap in the previous derivation.

**Incoming.** Every capacity-changing reserve has established checkpoint headroom for E_before+1. Consequently induction over admitted events gives `G+E≤M` and `J+E≤M`, regardless of whether their rows survive. Because event recording itself now has pre-reserve headroom, each changed surviving lane has at least one recorded event: K≤E. Both intermediate survivor checks G+K/J+K fit. The final G+E/J+E assignments fit as well. This includes the earlier review's failed-growth-on-a-dropped-row case.

Thus both branch inequalities are source consequences of the local guard; there is no need for an amortized theorem bounding lifetime counts by current allocations. Counts may be saturated at entry. A full-lane reserve then fails **before** capacity changes; operations using existing spare capacity remain admissible.

## 4. Compose the consumer result and state the limit

Sections 1–3 establish every checked subtraction/multiplication/payload addition, every per-survivor growth/rebuild increment, and the final branch history additions. Each reconciliation call therefore returns Ok, and none of these sites writes `accounting_error`. Its initial None reaches the final return unchanged. The computed payload is the exact current survivor charge; physical capacity growth and historical peaks need not equal their entry values.

Under R, this is a constructive derivation of the **late accounting component** for all constructor-valid histories in the assigned owner domain, including failed routes. It does not derive unconditional whole rollback return: preceding semantic inverses, Local/refresh reachability and the original wider source/scheduler domain have their independent obligations. Whole-session sampled totals and their publication are also different fields/consumers; exact nested bytes do not certify that entire census.

The earlier missing compiler premise—pre-reserve history headroom—has actual constructive evidence after the repair. The byte premise is now reduced to R's runtime applicability, with entry-census preservation derived rather than assumed. The installed library grounding supports R but does not verify the linked runtime or allocator binary. If unconditional actual-binary correspondence is required, that applicability is the exact remaining runtime premise; another compiler ledger reconstruction would not establish it. No counterexample or new semantic restriction follows.

This is not a third equivalent search against the old premise: its owning construction changed. The proof uses that new guard and proves the failure-history invariant. W/A3, incidence, lifecycle, complete Call meaning, effect hygiene, soundness, required principality and production cutover remain OPEN. The primary alone may adjudicate the narrow result after fresh independent review.

## Independent review and adjudication

Fresh compiler-referee review of the frozen artifact at SHA-256
`b01c8f7f45b91ae604eff27a38bfb02688e3f4e84a53e5fd54e7264794347931` found
no blocking, major or minor findings within its stated conditional scope. The
review supports the guarded incoming/nonincoming counter inequalities, the
failure-inclusive nested-byte induction, and the non-circular treatment of
early rollback exits. It considers R sufficient under ordinary valid Rust
allocation semantics, while confirming that actual linked-runtime/allocator
applicability is unverified. The primary accepts this only as a conditional
late-ledger lemma under R; it does not certify the unidentified binary or
promote original W/A3.

Semantic inverse totality, full rollback return, sampled whole-session
accounting, scheduler/incidence correspondence, lifecycle/§7, complete Call,
effect hygiene, soundness, required principality and production cutover remain
outside this review and OPEN.

## Frozen dependencies, checks and resources

The yulang-proofs skill and role/config pins were read by this continuing leaf. The current orchestration proof/model sections, research-lab evidence/stop policy, design-authority sources and compiler-engineering economy rules were reread; the unchanged relevant policies are carried forward. No coordination exception was granted. Requested runtime: ordinary prover, `gpt-6.1-sol`/high; observed effective model/effort **unknown**. No Astra, hot reload or override claim.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| Reviewed headroom derivation | `28f595f0bf3b787d6c173dce7ee2a567e6790322626b28a44b4cc1a03741c51e` |
| Frozen W/A3 falsifier | `093f2d3ef7ea4d3b206939c5dc8475cfbe793e25f3c01682c5b06d4f2afa59ad` |
| Original composition | `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222` |
| Handoff derivation | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Reviewed rollback lemma | `2d526b7df88acedd18c306e6ae5bad15314eed6451d4dd87eddc53c74711cdf7` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |

External read-only library snapshot root: `/home/momota1029/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/`. `alloc/src/vec/mod.rs`: `11ae2680d2cd4b58528ef608c1a3a3607fb0a20dc9f4bfd21d0a2d270b9cf572`; `alloc/src/raw_vec/mod.rs`: `76011c902ab137f3c1ab91432133d1f4ff6038e33fa60bf62a5e325bd12981a4`; `core/src/ptr/mod.rs`: `235e257e5a5491f90716fdb73af537b604c716486be04240371885eea58e3601`; `core/src/alloc/global.rs`: `d497414acb43282c4b281b27b7dcbfb945b71be4219b816eca2ebfa55d646de3`. Actual binary linkage unverified.

Checks: plain-file HEAD/ref resolution, exact input hashes, bounded rule/source/library reads, counter-writer and nested-capacity owner searches, constructive arithmetic/ownership induction, final dependency and note scope/whitespace checks. No Git commands/mutations, tests, builds, Cargo, executable probes, measurements, formatter, code/test/shared-record edits or delegation. The primary-reported focused checks remain separate evidence. Initial broad captures were truncated and decisive regions reread in smaller captures. One leaf, short read/hash processes; zero sustained computation or performance samples; CPU/RSS unmeasured. Packet started at 01:31 UTC and stopped within its 20-minute ceiling.

One next action: apply this reviewed conditional late-ledger lemma to the
original W/A3 bridge while keeping its semantic inverse, source/scheduler,
incidence and lifecycle premises OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-wa3-postrepair-ledger-proof.md`.
- Baseline SHA: `d7e87c63723213550ac28ddab45e2ef47ce17f6e`.
- Changed dependency hashes: none authored by this leaf; postrepair hashes above replace the prior proof's lib/extrusion inputs. The primary advanced the branch ref to `34b1c059f6ec91a472516d21f6cecaebc109668a` during this packet; all governing source/proof hashes above remained unchanged at final check.
- Claim/review status: independently reviewed constructive operational derivation under R; no binary certification or parent promotion. Actual runtime applicability and original W/A3 remain unverified/OPEN.
- Checks already run: exact hashes, operational-owner/constructor/consumer inspection, library grounding, static induction and leased-note checks. No executable verification.
- Proposed checkpoint message: `research: derive retained rollback ledger arithmetic after headroom repair`.
- Shared-record deltas left to primary/curator: record the guard-derived branch inequalities and failure-inclusive nested-census induction; distinguish the R runtime premise and whole-session sampled census; retain semantic inverse/scheduler/lifecycle and parent W/A3 OPEN. No shared records edited.

Artifact frozen after final checks. No further writes planned.
