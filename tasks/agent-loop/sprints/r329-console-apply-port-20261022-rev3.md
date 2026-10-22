# Sprint R329 — Console Apply-to-FreshUse port trace

Revision 3 preserves the exact Apply-port result and the role-frontier
normalization. Revisions 1 and 2 remain immutable intake and investigation
receipts.

## Established path

The Console Apply retains exact callee, argument, result and effect endpoints.
Its negative function demand carries the positive argument endpoint and
negative result endpoint. The imported `std::io::console.say` scheme transports
its formal parameter, `where 'a: Display`, and nested `value.show` receiver in
one authenticated FreshUse.

The top-level named group's unit annotation applies to its exact terminal body;
the outer Lambda separately links to the definition root. This source-derived
construction makes the unchanged Console `show` receiver read back as positive
`Int` after selecting the source-backed `int.add` result.

The exact `int.show` target and complete implementation inventory are present.
Selection remains pending because the receiver frontier has one negative row
edge to the same-FreshUse Display subject, zero exact negative bounds, and four
positive bounds. The edge is source-authenticated, but later-bound stability of
the receiver/subject pair remains open. The empty-frontier selector has not
been relaxed.

Repeated graph capture duplicated a role identity in the FieldTail's
`required_roles` vector. That vector now deduplicates role identities as a set;
all source `where` records remain separately retained and validated. The
focused Console readback stays pending at the single negative edge.

## Next exact question

Prove the receiver/subject pair remains stable under later bounds and all
source-bound consumers. Keep selection fail-closed until this is source
qualified. Then continue Console through `show`, host writes and execution,
followed by all remaining samples and the original source/native proof gates.

## Verification and limits

`cargo test -q -p yu-playground` passes all package groups (45 library tests,
23 CLI tests, and the remaining integration groups). Console output
`hello from Yulang\n3\n` remains unobserved. R149, all-sample execution,
source/native adequacy, theorem closure, independent review and production
remain open. Solo scope; no subagents, reviewer or prover lanes were started.

## Resources

Cap 2400 seconds, no carryover. Resource charge and artifact hashes live in
`tasks/agent-loop/current.json`.
