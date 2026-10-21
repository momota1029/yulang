# R289 outcome — module-qualified role/impl index for pinned Y2 library

# R289 outcome — module-qualified role/impl index for pinned Y2 library

The source-only index now covers all 40 files in the exact pinned Y2 stdlib closure. It found 19 direct-root roles and 86 standalone implementations. One role and four implementations carry parser-recovery flags, across `lib/std/data/list.yu`, `lib/std/text/str.yu`, and `lib/std/data/fold.yu`. Parsing reported 342 diagnostics in total under per-module syntax environments derived from direct pinned import headers.

The index preserves module-qualified parse-owned IDs, verifies unique module/role/implementation identities, parent ownership, and source slices. Recovery flags are retained as provenance; they do not admit those declarations to semantic use. The index is limited to direct-root roles and standalone implementations; nested attached implementations are not included.

This inventory does not establish import resolution, visibility, conformance, candidate selection, constraints, execution, source/native correspondence, or proof. Unchanged Y2 playground sample execution and proof remain open. The 342 diagnostics also mean this result is not evidence of full-library parse or type correctness.
