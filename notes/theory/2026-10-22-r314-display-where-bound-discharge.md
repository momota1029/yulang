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

## Captured Member FreshUse route

The graph layer now derives each captured Member FieldTail's four graph-row indexes with the same helper used by `prepare_candidate_fresh_use`. The same-session inspection API can return those source identities, graph owners, and local/shared-row flags together with root receiver readbacks. This layout is not an instantiated use and it does not type or select a member.

Two concrete results bound the route. First, the solver fixture with one nested FieldTail in each of a role-default and implementation member captures two distinct member graphs; their source occurrence/owner and all four FreshUse row indexes agree with the graph's exact rows. The focused solver test passes. Second, the unchanged pinned Types session returns `captured_member_graph_count = 0` and no captured member FieldTail rows. Its provider projection follows imported value `Name`s; the role/implementation inventory is retained separately from provider HIR, so the exact tuple implementation body never enters that solver session.

HIR now has an exact-source-key member projection entry point. Its focused test chooses one implementation member from the authenticated role index and confirms the resulting HIR contains only that exact member carrier. Attempting to add the entire pinned fmt member module fails during import resolution on unrelated routes. Adding only the selected member carrier lowers successfully, but the candidate inference entry point returns `Unsupported` for that whole-module HIR; the remaining preflight/collection owner has not yet been isolated. This keeps the next step concrete: admit the exact selected member-only HIR into the same candidate session without importing unrelated fmt direct roots.

## Evidence and open gates

### Exact member-body admission boundary

Revision 6 inspected the pinned implementation member original source: `our value.show = case value: (a, b) -> "(" + a.show + ", " + b.show + ")"`. The earlier rev5 attribution to tuple-pattern formation was too broad: the flat ordered tuple case pattern is already represented by `LocalSourceCasePattern::Tuple`. The exact blocker is the four-use infix chain. `Builder::expression` retains an `InfixOperator` only when an `OperatorChain` has exactly one `InfixOperatorUse`; the multi-operator chain therefore returns `Unsupported(UnsupportedForm)`. Candidate collection schedules only `Supported` member carriers, so this implementation body cannot enter a member graph. The pinned `Display.say` role member is also unsupported, but this probe did not isolate its precise constructor. R308 authenticates imported `+` to its exact provider declaration/body; that link does not assign a candidate scheme or select a method. Keep FieldTail selection deferred while the source carrier preserves the parser-associated operator tree and every operator/source identity.

- `cargo test -p yu-playground --lib unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session -- --nocapture`: passed. The exact pinned module session finds ordered `(Int, Str)`, target `('a, 'b)`, substitutions `'a = int` and `'b = str`, and both exact `Display` where-role identities. Each where subject has one matching source implementation (`int` / `str`) with no further prerequisites. The complete exact-role inventory has 16 implementations across `fmt`, `text::path`, and `time`; three application targets remain unshaped, so `unsupported_target_count = 3`. Ordinary inference still returns `DeferredSelectionUnavailable`.
- `cargo test -p yu-hir --lib`: 163 passed, including the existing cross-module role identity test.
- `cargo test -p yu-playground --lib`: 41 passed.
- `cargo test -p yu-hir --lib selected_member_source_projection_keeps_one_exact_implementation_body`: passed; `cargo test -p yu-hir --lib`: 164 passed.
- `cargo test -p yu-solver --lib member_sources_form_separate_candidate_roots_with_receiver_inputs --features shadow-apply-candidate`: passed, including the two captured Member FreshUse row layouts.
- `python3 tools/agent_sprint.py check` and `git diff --check`: passed after this note/current synchronization.
- Pinned source census: `fmt` supplies concrete `int` and `str` `Display` targets; `text::path` and `time` add other source-qualified candidates. All 40 bundle blobs remain pinned.
- Open: admit the exact selected Member-only HIR into the same candidate session; apply concrete where-prerequisite evidence to its FreshUse instance; general application-target shape matching; completeness of implicit-prelude member discovery across skipped ambiguous/unsupported/recovered routes; later-bound selection stability; Types output; Console; source/native proof and independent review.

No theorem, semantic rule, method selection, or production behavior is closed by this source census.
