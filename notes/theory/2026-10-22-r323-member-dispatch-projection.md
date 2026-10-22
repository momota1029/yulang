# R323 — exact member projection and FieldTail dispatch

## Parent obligation

Run unchanged Yulang2 samples through ordinary inference and execution, with the original proof and source/native obligations intact. Types remains the critical path; its `pair.say` use has not selected a member or inferred successfully.

## Prior evidence

R321: exact pinned `Display.say` source identity enters the candidate world and is captured as a same-session MemberGraph. Its nested `show` FieldTail has a FreshUse row layout. The unchanged consumer `pair.say` remains deferred.

R322: `FreshUse.source_field_tail_obligation_rows` has no solver consumer that uses its four rows to freshen a member graph and connect receiver/result/effect interfaces. Source inventory returns exact override-member identities but does not select or project their bodies into candidate schedules. The solver ends with the obligation pending.

## R323 question

Can exact implementation override member source be projected into candidate member templates before execution, and can a complete uniquely applicable FieldTail dispatch consume one template through a single shared-row FreshUse? Types requires the exact ordered-pair Display body and exact `Display int` / `Display str` prerequisites. Incomplete/ambiguous evidence must stay deferred.

## Source-owner trace so far

The public HIR projection entry accepts exact parse-owned member declaration keys, and lowering rejects keys not owned by the supplied ParsedFile. `MemberSchedule` separately records exact role-default and implementation-member identities; the plan has unique-by-identity lookup helpers for each. The source role implementation inventory carries an optional exact implementation override key, or explicit absence for a role default.

The projection boundary currently lacks a path from that candidate inventory to parsed source: `SourceRoleImplIndex` retains indexed declaration identities and source shapes but not the `ParsedFile`; `CandidateInference` receives already-lowered HIR modules. The playground provider projection currently follows imported binding exports and operator owners, not role implementation member candidates. Thus it cannot lower a late-selected override from inside the solver. The end-to-end path needs the source-world owner to pre-project exact candidate override bodies by their parse-owned keys, then the solver must choose one from complete receiver/prerequisite evidence and consume its graph with a single FreshUse. This split is a dependency, not permission to select by spelling or to compile every unrelated module root.

The solver-side FreshUse consumer remains absent as recorded in R322. R323 stays OPEN; no implementation or successful sample inference is claimed from this read-only trace.

## Proof boundary

HIR projection, candidate graph capture, readback, and tests are implementation evidence only. Independent review, source/native A/B, later-bound stability, R149, successful unchanged Types/Console, original theorem closure, and production authorization remain OPEN absent their own evidence.

## R323 implementation result

The source-world projection now discovers exact role-default member declarations referenced by retained FieldTail names and projects their owning module/member operation into the candidate world. It also gathers exact imported and authenticated implicit-prelude implementation override keys for receiver-applicable candidates, projects only those exact body members, and deduplicates identical provider projections. Abstract signatures and unrelated overrides are not projected as bodies. Source target parsing now retains prefix applications such as `list 'a`, `opt 'a`, and `result 'ok 'err`, so the tuple receiver check does not confuse those targets with tuple implementations.

The playground's pinned Types readback confirms the exact tuple `Display.show` source key is present in the projected module and its nested FieldTail remains in the captured MemberGraph FreshUse layout. `cargo test -p yu-playground --lib`: 42 passed. `git diff --check` and `python3 tools/agent_sprint.py check` pass. This is implementation and test evidence only.

The bounded end-to-end outcome remains OPEN: `execute_candidate` still has no consumer for `FreshUse.source_field_tail_obligation_rows`. Captured member templates therefore remain uninstantiated at a FieldTail use; the unchanged Types sample stays deferred before selection and successful inference. Next work is a solver-owned, unique exact-identity dispatcher that remaps the four rows through one FreshUse and admits receiver, result, and effect relations while preserving deferral on incomplete or ambiguous evidence. The `[io]` contravariant interpretation remains `[io,'e]`, so `[state]` remains permitted.

Independent review, source/native A/B, later-bound stability, Console, R149, all-samples ordinary inference/execution, original theorem closure, and production authorization remain OPEN. The user prohibits subagents, so this work is solo and unreviewed.

## Solver consumer and the generic operator boundary

The solver now consumes a selected member graph through one retained `FreshUse`: it maps the same four receiver/result value/effect rows, admits the corresponding interface constraints, retains the use, and puts nested FieldTail rows back on the worklist. The source-world projection also projects the exact prerequisite override members using the same `where`-clause implementation identities. The unchanged pinned readback now sees four member graphs: the `Display.say` role default, the tuple `Display.show` implementation, and its exact `Display int` and `Display str` prerequisites. Two focused playground tests and `git diff --check` pass; this verifies capture/readback and preserved deferral only.

Dispatch then reaches a different source owner: imported standard-library infix `+` has the exact body `\\x -> \\y -> x.add y` in `lib/std/core/ops.yu`. Its `add` FieldTail belongs to the generic operator provider, whose receiver has no positive shape while that provider scheme is being constructed. The current worklist maps this source FieldTail through each operator FreshUse and correctly refuses to select without evidence. In the unchanged Types sample, standard-library operator-provider uses are included even though the sample's `pair.say` is the demanded expression, so this generic `x.add` currently leaves the whole candidate solve deferred.

The next source/solver obligation is to retain the open FieldTail as part of the operator provider scheme and activate it at the consumer use where actual receiver bounds have arrived, using that same use's row map. The current graph representation transports FieldTail rows but does not yet represent this delayed provider-template obligation through nested operator construction and instantiation. Eagerly selecting the generic receiver would violate the complete-evidence gate; dropping the obligation would erase source constraints. Types and successful inference therefore remain OPEN. This is a source-correspondence and candidate-scheme lifecycle premise, not proof closure. The `[io]` reading remains `[io,'e]`; `[state]` is allowed in the contravariant position.
