# R313 — receiver-bound shape and FieldTail applicability

## Entry evidence

R312 reached RESULT with authenticated cross-module role and implementation member identity, solver transport of source-owned implementation targets, and a bounded structural shape for simple names/tuples. Its focused HIR and solver checks passed. The unchanged `Types` sample still returns `DeferredSelectionUnavailable`; R149 remains OPEN.

The pinned `std::core::fmt` `Display` tuple implementation target is `('a, 'b)` and its body has two `where` clauses, `'a: Display` and `'b: Display`. The exact role member `say` comes from the authenticated imported `Display` identity. The solver runs all direct source-expression schedules before reporting pending member FieldTails, so the intended evidence point is the same inference session immediately before the pending-selection gate in `InferenceSession::execute`.

## Current implementation facts

Candidate value rows retain direct lower/upper row edges and exact non-variable lower/upper endpoints in `VariableBounds`. Tuple source constraints become `PositiveTuple`/`NegativeTuple` term endpoints and are drained elementwise. A receiver-value row therefore cannot be classified from its row ordinal or one bound alone: relevant aliases/rows and every direct structural bound must be accounted for. Intrusion may canonicalize row identities. Any extraction must preserve tuple order and exact source relation/provenance, detect cycles or unexpanded row edges, and fail closed if the frontier is incomplete.

The solver's post-schedule gate currently checks only `GraphState::has_pending_field_tail_selection` and returns `DeferredSelectionUnavailable`; no public candidate result escapes. The next implementation seam is a private readback at this point that identifies actual receiver bounds in the current session without constructing candidate types. Selection stability still needs a separate argument: newly admitted legal constraints cannot change the chosen implementation while the member template is being instantiated, or the obligation must remain deferred.

The R313 prototype adds a test-only `InferenceSession` readback for the unique common positive lower shape of a value row. It follows canonicalized direct lower-row edges, recursively reads positive tuple terms in element order, ignores positive bottom, and returns unavailable for cycles, missing/unsupported shapes, or conflicting concrete lower shapes. A focused local source fixture with `my pair = (1, "x"); pair.echo` confirms the post-schedule FieldTail receiver row reads as `(Int, Str)` while the pending gate still returns `DeferredSelectionUnavailable`. This is evidence about the current lower-bound snapshot only; it is not a source/production method selection rule, does not inspect negative bounds, and does not prove future stability.

Implementation where preambles now retain an ordered `Option<SourceImplementationWhereClause>` per exact source entry. Supported clauses carry exact source-owned subject and role types. Candidate resolution also retains an ordered exact `SourceRoleId` for each supported where-role head, resolved through the implementation module's imports; unsupported or unresolved clauses keep `None`. The authenticated pinned `Display.say` candidate inventory preserves the tuple implementation's two obligations, `('a, Display)` and `('b, Display)`, and both heads resolve to the exact pinned `Display` identity. Its explicit absent `say` override keeps the role default separately identified. Candidate plan byte accounting includes the cloned prerequisite inventory, role-ID slots, and shapes. No obligation is discharged yet.

The unchanged 142-byte playground `Types` sample now has a readback from the exact pinned-import module world and the same solver session that reaches `DeferredSelectionUnavailable`. It finds the ordered receiver shape `(Int, Str)`, visits the positive lower frontier completely, and finds five reachable positive endpoints with no reachable upper-row edges or upper endpoints. The authenticated implicit-prelude `Display.say` path identifies the exact local tuple implementation target `('a, 'b)`, the substitution `'a = int`, `'b = str`, and both exact `where` role identities as the pinned `Display` declaration. Three other implementation targets in that local role inventory have unsupported shapes, and the role/member inventory is explicitly marked incomplete. This is structural receiver and prerequisite evidence only: no `where` obligation is discharged, no candidate is selected, and no future-constraint stability is established.

The readback path enumerates source-authenticated role members exported through `std::prelude`, retaining all matching members as candidates. For this provisional evidence pass, implementation inventory for an implicit-prelude role is bounded to that exact role declaration's source module. This lets the authentic `fmt` tuple implementation be inspected despite unsupported role-import syntax elsewhere in the pinned library, but it cannot prove global method lookup uniqueness or stability. Normal `solve_modules_with_role_sources` still defers the sample unchanged. Do not promote the bounded local inventory into a method lookup rule.

## Plan and evidence

1. Build a bounded, ordered structural readback over the receiver row's positive and negative bounds, following exact row aliases only when the frontier is complete. **Done for the exact pinned `Types` session**; this reports its current snapshot and does not prove future stability.
2. Match the readback against the source-owned `SourceImplementationTypeShape`; support only proven forms and preserve explicit unavailable outcomes. **Done for the exact ordered tuple target**; three unsupported local targets and incomplete global inventory remain visible.
3. Parse/authenticate both generic `where` obligations and discharge them against the same receiver element evidence, with no candidate-body trial typing. **Identity and subject matching are exposed; prerequisite discharge remains open.**
4. Prove unique applicability is stable under later admissible constraints, or keep the current deferred boundary. **Open; selection remains deferred.**
5. Only after that gate, connect exact implementation member identity to `MemberSchedule`, instantiate the Member graph with one FreshUse for all four ports, and drain its nested obligations.

Checks and limitations will be appended with exact commands. No sample, proof parent, review, or production gate closes merely from structural readback or green tests.

## R313 checks so far

- `cargo test -p yu-solver --features shadow-apply-candidate --lib post_schedule_readback_recovers_receiver_tuple_shape -- --nocapture`: passed; local source fixture only, still deferred.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib types_sample_fieldtail_receiver_bounds_expose_ordered_pair_shape -- --nocapture`: passed; the `id`/`answer`/`name`/`pair.say` source-shaped fixture reads its positive and negative direct frontier after schedule drain, still deferred.
- `cargo test -p yu-playground --lib pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions -- --nocapture`: passed; authentic pinned role/implementation identities and both tuple `where` prerequisites remain source-linked.
- The same pinned playground test now confirms both tuple prerequisite role heads resolve to the exact pinned `Display` role ID.
- `cargo check -p yu-solver --features shadow-apply-candidate`: passed with existing warnings.
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`: 57 passed.
- `python3 tools/agent_sprint.py check` and `git diff --check`: passed after where-clause candidate wiring.
- `cargo test -p yu-playground --lib unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session -- --nocapture`: passed; exact pinned module session, ordered `(Int, Str)` receiver, exact `('a, 'b)` target and both exact `Display` where-role identities; three unsupported local targets remain and inventory is explicitly incomplete.
- `cargo test -p yu-playground --lib`: 41 passed. This validates the bounded readback and preserves the ordinary deferred boundary; it does not prove lookup uniqueness, prerequisite satisfaction, stability or execution.
- `cargo fmt --all -- --check`: not usable as a focused check because it reports broad pre-existing formatting drift across unrelated workspace files; no formatter was run and no unrelated paths were changed.
