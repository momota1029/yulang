# Ordinary HIR binding-carrier formation

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Implementation baseline: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`
Status: HIR formation and original local proof complete; solver integration OPEN

## Authority and implementation

The [Authoritative carrier design](../design/2026-10-10-ordinary-hir-successor-carrier.md)
selects supplementary source formation after ordinary lowering. Its direct
continuation record preserves the archived approval receipt's exact-text
rejection without requesting the same technical approval again. The archive
is unchanged and no pending question enters this checkpoint.

`lower_module` retains all original admission flags, items, namespace,
diagnostics, definition/parameter identities and ordinary occurrence order.
After that phase it forms one Supported/Unsupported outcome per admitted
binding in root order. Each attempt owns private identity maps, builder arenas
and a cursor. Unsupported source discards that attempt and continues; genuine
identity/allocation/internal errors remain availability failures. Success
orders supplementary occurrences by actual CST preorder and atomically merges
all staged maps. Terminal failure publishes no module; arbitrary allocator
abort recovery or retry restoration is not a theorem premise.

`source_identity.rs` is an ordinary owner. Default exports and branded key/origin
accessors expose retained facts without requiring the shadow feature or
reconstructing source. Existing shadow adapters retain their refusal/error
contracts. Root-indexed carrier lookup is constant time. Traversal and storage
are linear in visited source/formed records, plus actual payload-copy costs;
no growing module state clone or second parse was added.

Ordinary rejected Act declarations remain rejected. Resolution is authentic to
the actual completed ordinary namespace, which is not the expanded opt-in
namespace. This implementation does not expand root headers, admit new syntax,
select a solver or remove an F5 consumer.

## Proof and independent review

The [preservation proof](../theory/2026-10-15-ordinary-hir-carrier-preservation.md)
discharges its original five conclusions over ordinary inputs: preserved
ordinary projection, exact binding outcome coverage, original identity/CST
ordering, complete private mutation/publication discipline and foreign-brand
rejection. Source refusal and genuine availability remain distinct. It checks
every builder writer, syntax key producer, actual pinned Rowan traversal,
annotation failure owner, source map merge and consumer.

M2 uses `ordinary_carrier_semantic` and `ordinary_carrier_contract`. The sole
major finding was three tests still assuming ordinary provenance was absent.
The approved design supersedes that absence premise: the tests now assert
successful ordinary lookup, then remove their test-owned sidecar to retain
MissingSource controls. Foreign-brand controls and test names remain. The
colon-helper expectation retains StructuralProjection through its exact error
adapter. Minor mixed-root/inline/operation baseline controls were added. Both
delta reviews are clean; fresh proof review accepted artifact
`29a6ab734a2dc37d48613fc312941d37c7ccac05da46c34e3a75b07de1cf63af`.

Initial default compilation exposed ten dead-code warnings. Precise feature
gates now cover genuinely shadow-only consumers; ordinary provenance accessors
consume retained source evidence. No blanket warning suppression was added.
The separately reviewed literal-owner correction is preserved byte for byte
apart from its typed FormationError adaptation.

## Verification and integration

Primary-only Cargo, two build jobs, 300-second timeout, test threads two:

| Command | Result |
| --- | --- |
| `cargo check -p yu-hir` | isolated and integrated main pass, no warnings |
| `cargo check -p yu-hir --features shadow` | isolated pass, no warnings |
| `cargo test -p yu-hir --lib ordinary_ -- --test-threads=2` | 7 pass |
| `cargo test -p yu-hir -- --test-threads=2` | integrated main full suite passes |
| `cargo test -p yu-hir --features shadow -- --test-threads=2` | 201 pass, including 128 unit and 5 compile-fail doctests |
| `cargo test -p yu-solver --test ordinary_source_carrier -- --test-threads=2` | 1 pass; exact carrier and ordinary IDs retained/exposed by default collection |

Full verification found two sibling expectations requiring source-based
maintenance: the stale October 5 grouped-application subset, repaired separately
in `b5031d2fc`, and trivia-bearing inline literal payload equality, repaired
separately in `c7e56d0f0`. Both received pre/post specification review; no
expectation was altered merely to match an unexplained output.

Five copied source files exactly match the isolated reviewed freeze; the sixth,
`source_identity.rs`, only drops an extra EOF blank line. Integrated `lib.rs`
differs only by the separate test repair and new-export line wrapping.
No timing/RSS experiment ran (zero samples). Full solver/backend suites were
not run; a fresh workspace check belongs to the following runtime/shared phase
boundary, where runtime code is currently being edited on disjoint paths.

## Next owners and records

The default solver probe uses only ordinary APIs and confirms exact Arc/carrier
pointer identity, branded roots, source-key correspondence, distinct authentic
ordinary occurrences and foreign-root rejection. It received pre/post contract
review. Cargo dev-dependency unification enables HIR shadow through yu-core;
the command uses no experimental solver feature, but is not evidence that all
dependency shadow features are absent. Retention/access is not successor
constraint consumption. The design's stronger consumption requirement remains
for that actual integration. General expression-root ownership, full Call and B,
receiving hygiene, native soundness/principality and production/F5 withdrawal
remain OPEN. Current task, research-lab, design status and index are synchronized.
