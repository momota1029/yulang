Sprint-ID / contract revision: EFFECT-PERMISSION-STRUCTURAL-BUFFER-BOUND/20261029-r18; rev1.
Assignment-ID / handoff revision: R18-source / rev1.
Parent gate / scope: inference/executor soundness remains OPEN. This source trace asks whether one selected tuple construction can overrun the six-slot event buffer before its wrapper drain.
Baseline / direct dependencies: R17 artifact `1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57`; R17 manifest `53052f07b01674a05ad9c2511dbe3fb9319ee6922183baf0dd2c27bf520b40ae`; R17 source mapping `0324a286e294ce711c6f09fba0371a041032c4d25c7d66f3319d66a89a40ae08`.
Role / owner: primary Luna source lane, read-only on Rust and existing Lean sources; no child or runtime worker.
Requested/observed model and effort: Luna/high primary; runtime metadata unavailable.
Exact write path: this handoff only. No Rust file was written.

## Source mapping and event sequence

At `candidate_effect.rs:1617–1659`, a nonempty tuple annotation recursively maps each child through `candidate_formal_value_pair`; the base Bool/Str/Int/Unit cases use terms from the sealed collected lineage. `BranchTermArena::lookup` (`term.rs:831–850`) resolves a matching brand and collected-prefix index before looking in postfix pages, so such collected children can be validated without first allocating a postfix term. The tuple branch then invokes `with_term_events` separately for `positive_tuple` and `negative_tuple`.

`positive_tuple` checks nonempty children and looks up each polarity-compatible child, copies the backing, then calls `intern_structure` (`term.rs:1272–1303`). A cache hit in `intern_structure` returns before reserves or append. On a cache miss it checks payload size, calls `structural_backings.try_reserve(1)`, then invokes `intern(node)`.

For a route-journal-active, page-needing, cache-miss `intern`, five successful reserve operations can each change capacity and record one snapshot: interner `positions`, journal `interned`, page descriptors `pages`, page-position directory `page_positions`, and journal `claimed_pages` (`term.rs:1166–1201`, `1083–1158`). The new fixed page then unconditionally appends its PageBacking snapshot (`term.rs:1145–1152`), giving six events when all five capacities grow. After `intern` returns success, `intern_structure` publishes the backing and unconditionally appends the structural-owner snapshot (`term.rs:1371–1382`), independent of whether `structural_backings` capacity changed. With a starting empty buffer, that final push calls the six-slot assertion with `len == 6` and panics before control returns to `with_term_events`.

`with_term_events` drains only after the constructor closure returns (`lib.rs:10594–10622`). Therefore it cannot drain this seventh attempted push. A successful structural reserve, five successful intern/page reserves with actual capacity changes, a successful page allocation/claim, valid children, a cache miss, active route journal, and empty event buffer are all required premises for this conditional sequence. The reserve calls use `try_reserve`; their successful return alone does not prove growth. `TermPage::try_new` uses the global allocator and can fail before PageBacking is appended. `claim_page` can also fail before the page is published. These are not abstract Boolean events: each must be tied to its actual primitive result/capacity observation in any Lean trace.

## Route and reachability boundary

`TermBuilder::seal` creates a collected prefix and initializes the shared postfix allocator (`term.rs:380–395`); `BranchTermArena::new` starts with an empty event buffer (`term.rs:707–723`). `begin_route` activates a journal (`term.rs:746–777`). `Session::begin_route_transaction_for` reaches `store.begin_route`, which invokes `terms.begin_route` (`lib.rs:9267–9310`, `3503–3505`). These establish local source transitions, but this audit did not authenticate the complete external candidate call chain that simultaneously supplies an active journal, a fresh structural tuple cache miss, exact capacities forcing all five growths, and successful allocation/page claim. The tuple route is an obstruction candidate, not a native counterexample.

The exact conditional event count is **six intern events followed by one structural event**. The concrete `intern_structure` implementation does not impose a global six-event guard on event generation; instead, the buffer push asserts before storing the seventh. No source invariant found in the inspected functions excludes the six-growth combination. This remains a conditional source trace until the Lean model proves its arithmetic/transition obligations and a separate source/native bridge authenticates the candidate call and primitive outcomes.

## Parent application and remaining premises

What follows: R17's physical buffer model identifies the exact failing operation; source code supplies a realizable local operation order and the necessary reserve/growth/publish premises. The relevant failure is a panic before `with_term_events` drain, not a normal constructor `Err`.

Still OPEN: actual simultaneous growth on an admitted candidate route; exact caller-level active-journal and cache state; allocator availability and page-claim outcome; full source/native execution correspondence; whether any other source invariant excludes this trace. This packet does not authorize behavior changes or production conclusions.

No tests, Cargo, Rust execution, instrumentation, Git operations, or source edits were run. No descendants. Source writes stopped.
