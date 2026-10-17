# Applied compiler review: ordinary HIR repair candidate

Sprint `ordinary-hir-applied-conformance-repair-20261017` rev3, candidate
commit `5d9ecdfff75d2b93de5b33958496ad9f82586bff`, handoff revision 4 SHA-256
`2aa369b9efc59e42ee8951a1bcf2f3f28b332791a800215f052ee594362bfa37`.
Reviewer `/root/ordinary_hir_repair_applied_compiler_review`,
`compiler_referee`; requested gpt-6.1-sol/medium, observed model/effort UNKNOWN;
STOPPED. Exact elapsed UNKNOWN; Luna charges full 180s cap. No source edits,
tests, builds, probes, external contact or descendants. Reviewer disclosed an
inadvertent read-only `git status`/`git show` during orientation despite the
assignment's no-Git instruction; no Git mutation occurred.

The reviewer verified all supplied pins. Changed implementation hashes:

```text
lib.rs      a50d7b70c76906e009c0a7f7ae74c29f485d6e65365e0f29c2c7e0dc8b481cee
module.rs   1644c4d1ceffde5780737f87bee9f1fca1bdfc35a8b332dcd9556679462e4ac4
HIR test    dd6c2ac5f5e8b50e37637a84e3f7427a1f628cd0f8edcaa2803775ab702ba972
```

## Result

No BLOCKING or major finding. The seven prior findings are addressed in their
owning code paths: causal refusal preserves errors; real CallTail/Group
punctuation is checked before operand resolution; operand errors are staged
after duplicate-definition and receive dense final IDs; binding class follows
the replaced value; association carries actual source nodes without public
HIR changes or range lookup; finalization uses a saved item index; grouped
fixtures retain authentic unresolved diagnostics and exact parse-owned keys.
Static output-sensitive accounting supports `O(V+E+R)`. Apply lists are
assembled once in child order and Groups do not materialize copied error lists.
No run evidence exists; tests remain unrun. Standard Apply/Group constraint
collection remains incomplete, and no Call/theorem promotion follows.

One **MINOR conformance finding** remains. In `module.rs`, `identity.append_stage(stage)`
occurs before validating the saved item index, binding kind and placeholder
root, and before the checked visit-counter increment. A malformed private
admission therefore returns `StructuralProjection` after mutating the private
source-identity accumulator. No valid-source trigger was found and
`lower_module` returns no module on the error, but this violates repair
invariant 6 and the architect's validate-before-merge requirement.

Required repair: validate the indexed binding and exact placeholder root, and
check the counter increment, before `append_stage`; then perform the validated
replacement. The seven-path candidate lease is frozen and its author STOPPED.
Any repair requires Luna's sequentially granted exact follow-up lease and fresh
implementer acknowledgment. Run compiler delta review after that one-line
ordering change, then continue the already authorized spec, architect and
regression reviews. Original theorem conditions closed: 0.
