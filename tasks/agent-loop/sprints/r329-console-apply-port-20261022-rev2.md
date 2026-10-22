# Sprint R329 — Console Apply-to-FreshUse port trace

Revision 2 records the result-annotation source constructor and the remaining
selection frontier. Revision 1 remains preserved as the intake contract.

## Parent and scope

The parent objective remains all unchanged Yulang2 playground samples working
through ordinary inference and execution, with source/native proof. Preserve
the source and native quantifiers and all design/proof gates. R149,
source/native adequacy, theorem closure and production remain open.
Contravariant `[io]` means `[io,'e]`, admits `[state]`, and leaves performed
state in the residual.

## Established source-to-candidate relation

The Console Apply retains its exact callee, argument, result and effect
endpoints in `CandidateRelation::Apply` and `NativeInterface`. Its function
demand carries the Apply argument in the positive argument port and the result
in the negative result port. The imported `std::io::console.say` graph retains
the declared formal, `where 'a: Display`, and nested `value.show` receiver in
one authenticated FreshUse map.

The LocalSource named group for `say` identifies the exact Definition owner,
first formal Lambda and terminal body. Its explicit unit annotation is a
result annotation. The candidate schedule now applies it to the terminal body
and separately links the outer Lambda to the definition root. The unchanged
Console `show` receiver now reads back as positive `Int`, reached from the
selected Add result through the Apply/FreshUse port correspondence.

## Remaining exact question

The exact `int.show` target and complete implementation inventory are present,
but selection remains fail-closed because the receiver's reachable frontier
contains one negative row edge (receiver row 89 to upper row 90). There are four
positive bounds and no exact negative bounds. A same-route join maps row 89 to
the retained `std::core::fmt::Display` subject row 90. The active selection
record has two equal Display role identities, while its retained route graph
exposes one corresponding where-source record. Trace the duplication and all
consumers. Determine whether the edge is exactly the same-FreshUse Display
prerequisite and whether selection remains stable under it. Do not relax
`negative_frontier_empty` from shape equality or from role spelling.

After that relation is established, continue the unchanged Console sample
through Display selection, host writes, and execution, then proceed through all
remaining samples and source/native obligations.

## Verification and limits

The focused Console readback test asserts positive `Int` at the imported
`value.show` receiver before dispatch remains deferred. `cargo test -q -p
yu-playground` passes all package groups (45 library tests, 23 CLI tests, and
the remaining integration groups). The CLI has not produced
`hello from Yulang\n3\n`.

This result is implementation evidence only. R149, all-sample execution,
source/native adequacy, theorem closure, independent review and production
remain open. The solo scope continues; no subagents or reviewer/prover lanes
were started.

## Scope and resource receipt

The active changes stay within the existing held solver and playground paths,
this sprint contract, its theory note, and `tasks/agent-loop/current.json`.
Resource cap remains 2400 seconds with no carryover. Record actual charged
time in `current.json` at the next checkpoint.
