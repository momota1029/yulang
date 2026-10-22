# R314 — Display prerequisite discharge and source completeness

## Entry state

R313 is capped at 1800 seconds and preserved as an active, unreviewed checkpoint. Its exact pinned Types session reads the `pair.say` receiver as `(Int, Str)`, and matches the authenticated `std::core::fmt` two-tuple `Display` target. The two source prerequisites retain the exact local `Display` identity. The solve still returns `DeferredSelectionUnavailable`; it does not type or execute the method.

The converted unified design and proof companion were reread at R314 entry. They require preserving source identity with transported constraints, treating method selection as a deferred obligation until relevant bounds and stability are known, and keeping test evidence separate from source/native proof closure. The R149 source and expected output remain unchanged.

## New source census

Decoded the existing pinned standard-library bundle without changing it. In the pinned closure, direct `Display` implementations occur in exactly three modules:

| Module | Source targets |
| --- | --- |
| `std::core::fmt` | `int`, `float`, `frac`, `bool`, `str`, `char`, `unit`, `list 'a`, `opt 'a`, `result 'ok 'err`, and tuples of arity 2 through 5 |
| `std::text::path` | `path` |
| `std::time` | `instant` |

The `int` and `str` targets are the only primitive targets in this list that match the R313 tuple implementation's two substituted subjects. At R314 entry the cross-module resolver returned `UnsupportedRoleImport`: while resolving `std::time`'s `Display` implementation it treated the relative `pub use clock::*` as a top-level module named `clock`, even though the exact `time` source index owns `clock` as a non-module declaration and the pinned closure has no `std::time::clock` module.

The source resolver now skips a glob whose target has no module index only when the exact importer snapshot contains a same-named non-module declaration; recovered/unsupported imports and unresolved module routes remain errors. The authentic whole-world `Display` inventory now resolves all 16 implementations: fourteen in `fmt`, one in `text::path`, and one in `time`. The `path` and `instant` candidates remain present and source-authenticated; the importing module's local `clock` namespace no longer blocks unrelated role resolution.

## R314 question and route

For the exact tuple implementation, substitute each retained `where` subject through the target match, preserving source order:

| Source clause | Substitution | Required evidence |
| --- | --- | --- |
| `'a: Display` | `int: Display` | exact pinned `int` implementation identity and empty/discharged prerequisites |
| `'b: Display` | `str: Display` | exact pinned `str` implementation identity and empty/discharged prerequisites |

The same-session readback now carries each `where` subject's type-expression source key, subject shape, substituted subject shape, exact role ID, matching implementation IDs, and which matches have no further source prerequisites. For the exact tuple implementation it derives `'a = int` and `'b = str`; each subject has one exact `Display` implementation in the 16-entry authenticated inventory, and both concrete implementations have no `where` clauses. No candidate body is trial-typed. The three application targets `(list 'a)`, `(opt 'a)`, and `(result 'ok 'err)` remain source-visible but have no bounded structural shape, so the matcher keeps `unsupported_target_count = 3`. This evidence authenticates both generic prerequisites for the observed pair but does not close the general source type matcher or prove stable FieldTail selection.

## Member FreshUse and completeness boundary

The current readback entry point obtains its rows from `GraphState::source_field_tail_obligations` after the root source actions reach `DeferredSelectionUnavailable`. The corresponding captured `Graph` / member-graph obligations are retained and remapped by the existing FreshUse path, but this readback does not walk those captured graphs or apply the source prerequisite evidence to a fresh member use. The existing `deferred_field_tail_rows_survive_capture_and_same_freshuse_map` test establishes row transport through the map; it does not establish where-clause discharge for a captured member use.

The prelude-member census is not a completeness certificate: candidate collection skips missing and ambiguous prelude exports and skips unsupported/recovered routes, while the three generic implementation targets have no bounded structural shape in the current representation. The exact 16-entry inventory is complete only for the exact retained `Display.say` role-member identities. These skipped routes and unshaped targets remain blockers for global member completeness. No source spelling or declaration order is used to fill them in.

## Evidence and open gates

- `cargo test -p yu-playground --lib unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session -- --nocapture`: passed. The exact pinned module session finds ordered `(Int, Str)`, target `('a, 'b)`, substitutions `'a = int` and `'b = str`, and both exact `Display` where-role identities. Each where subject has one matching source implementation (`int` / `str`) with no further prerequisites. The complete exact-role inventory has 16 implementations across `fmt`, `text::path`, and `time`; three application targets remain unshaped, so `unsupported_target_count = 3`. Ordinary inference still returns `DeferredSelectionUnavailable`.
- `cargo test -p yu-hir --lib`: 163 passed, including the existing cross-module role identity test.
- `cargo test -p yu-playground --lib`: 41 passed.
- `python3 tools/agent_sprint.py check` and `git diff --check`: passed at the previous record synchronization; rerun after this note/current update.
- Pinned source census: `fmt` supplies concrete `int` and `str` `Display` targets; `text::path` and `time` add other source-qualified candidates. All 40 bundle blobs remain pinned.
- Open: apply where-prerequisite evidence to captured Member FreshUse rows; general application-target shape matching; completeness of implicit-prelude member discovery across skipped ambiguous/unsupported/recovered routes; later-bound selection stability; Types output; Console; source/native proof and independent review.

No theorem, semantic rule, method selection, or production behavior is closed by this source census.
