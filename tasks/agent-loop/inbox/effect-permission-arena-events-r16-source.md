Sprint-ID / contract revision: EFFECT-PERMISSION-ARENA-EVENTS/20261029-r16; admitted after the R15 sprint-end selector recommendation.
Assignment-ID: R16-source / rev1.
Parent gate: unchanged Simple-sub inference/executor goal; R15 term-call control theorem plus R12/R13 roots remain conditional foundations.
Pinned source: `crates/yu-solver/src/term.rs` SHA-256 `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`; `crates/yu-solver/src/lib.rs` SHA-256 `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `crates/yu-solver/src/candidate_effect.rs` SHA-256 `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717` (worktree differs from HEAD and remains a frozen read-only dependency).
Direct Lean dependency: R15 artifact SHA-256 `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7`; R15 full audit receipt SHA-256 `02eca0b48d30dd438a696cab015975bdcc89cc997e6e41df1108b453cb28378b`.
Role: primary Luna source audit, read-only on Rust and Lean dependencies; writes only this handoff. No worker launched in this source lane.

## Source derivation

`TermCapacityEvents` stores at most six ordered `TermCapacitySnapshot`s. `record_capacity_change(before, lane)` snapshots the full capacity vector after a reserve attempt and appends exactly when the selected lane capacity differs. Both `push` and `intern` call it before propagating the reserve result, so a reserve error can be preceded by a retained event if capacity changed. There is no event for a reserve attempt without a capacity change.

For `live_variable`, `positive_function`, and `negative_function`, the constructor eventually calls `intern`. A cache hit returns with zero new events. On a cache miss, `intern` first attempts the interner reserve, then the optional active route-journal `interned` reserve, each recording a changed capacity before returning an error. Only after those succeed does it call `push`.

If the current page has space, `push` appends the node and emits no further capacity event. If a new page is needed, it attempts, in order: page descriptor reserve; page-position reserve; optional route-journal claimed-page reserve. Each changed capacity is recorded before error propagation. After those reserves it allocates a `TermPage`, claims a page identity, inserts its position and publishes the page. Failures in page allocation or claim preserve earlier events and occur before the PageBacking event. After successful page publication, `push` always appends one PageBacking snapshot. This yields at most six new events for an uncached constructor requiring a page: Interner, optional InternedJournal, PageDescriptors, PagePositions, optional ClaimedPagesJournal, PageBacking. The order among the optional and page events is exactly the order above; absent capacity changes omit their snapshots.

`live_variable` directly interns its node. Positive and negative function constructors first validate four children with their respective kind/polarity constraints; a validation error produces no constructor capacity events. On validation success they intern the corresponding function node. Neither function constructor uses structural backing.

The supplied `with_term_events` call invokes the constructor, then unconditionally drains `take_capacity_events`, even after constructor failure. The drained sequence includes any preexisting buffer prefix as well as events appended during this constructor. It then samples in order only while incoming route accounting is active, stopping at the first sampler error; otherwise it drains without sampling. R15 models this control flow but does not establish the source-side constructor/event relation.

The formal derivation must therefore retain an explicit initial event prefix. Since the source buffer has total capacity six, a constructor that appends `k` snapshots requires `prefix.length + k ≤ 6`; no empty-prefix assumption is justified by these source sites. A failed reserve may retain a changed-capacity event, and later failures may preserve the entire preceding prefix. `take_capacity_events` resets the buffer after draining.

## Caller boundary

`candidate_formal_value_pair` creates a positive/negative live-value pair for `Variable` and `Hole` branches via `live_value_term`. For a `Function` branch it derives argument and result pairs, then argument and result effect ports, then calls positive followed by negative function construction using different polarity-selected children. This establishes the caller order only for this branch; it does not establish the provenance, validity, or successful execution of the child terms. Other constructors (including tuple and structural-backed constructors) are outside R16's constructor protocol.

## Explicit unresolved premises

This handoff does not prove allocator or reserve semantics, that capacity changes are observable under every reserve error, availability of the term arena or sampler, provenance of the initial event buffer, authenticity of page identity claims, successful Rust execution, or correspondence from the caller to the R15 opaque constructor/event inputs. The exact `reserve_f5b` production behavior remains an explicit primitive premise. Test-only injected failures and observers are not production semantics. No Rust tests, Cargo commands, probes, instrumentation, or source edits were run.

Source work is complete; no descendant leases.
