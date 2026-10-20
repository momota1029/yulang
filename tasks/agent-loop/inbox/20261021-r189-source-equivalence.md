# R189 result — resumed suffix source equivalence

Status: RESULT, source comparison only. No code or semantic authority.
Contract: `tasks/agent-loop/sprints/resumed-suffix-test-equivalence-20261021-r189.md`.
Baseline: `183d69ef36cf45753980a83b7eecefd303421650`.

## Comparison

The two unchanged fixtures have the same relevant source structure:

```text
outer/relay (thunk:[io] int) = catch thunk {
  io::tick(p), k -> k <integer>
}
main = outer/relay (inner/helper {
  my local = io::tick 7
  io::other local
})
inner/helper (input:[io] int) = catch input {
  io::other(p), _ -> <integer result>
}
```

The differences are binder/definition names, the resumed integer (`23` versus
`11`), and the accepted handler result (`p` versus `99`). Both programs declare
the same `tick` and `other` operation signatures in a local `io` family; both
install the same ordered `other` handler around a delayed computation; both
first request `tick`, resume the saved suffix, and then request `other` with the
resumed integer. The `other` arm uses a wildcard continuation in both cases.

The differing arm result is evaluated only after handler selection. In
`propagate_request`, the positive local Grant check and the declaration/payload/
continuation-shape checks precede entering the arm body. Returning the payload
or a ground integer cannot distinguish whether that handler is selected. The
two fixtures therefore expose no source distinction in owner, observation,
event, boundary, annotated family, or ordered candidate that justifies opposite
event-1 Grant outcomes.

R188's recorded event-1 trace was owner `Invocation(4)`, observations
`(view 2, receipt 2)` and `(view 5, receipt 5)`, and retained boundary receivers
`[0, 1]`. Its temporary origin alias to `Invocation(1)` made both source shapes
eligible, so it violated the explicit expired-Grant guard. That experiment does
not establish which expected outcome is semantically correct.

## Parent application and remaining premise

The test expectations are in tension under the current source-observable Grant
premises: one requires the resumed `other` handler to run and complete with 23;
the other requires the same-shaped resumed `other` handler to fail with
`Unavailable(HandlerEvidence)`. No code, test expectation, or Grant rule was
changed. The remaining premise is the approved source meaning of an expired
receiver's Grant across capture/resumption and fresh owner re-entry. Its owner is
the existing semantic/design approval path, not this runtime investigation.

Parent theorem, A/B obligations, source/native correspondence, implementation,
and production gates remain OPEN. The source-equivalence finding is not a
counterexample to the parent theorem and does not approve relaxing either test.
No tests were run for this comparison. Pinned runtime/test inputs matched at
entry. Primary-only work charged 120s of a fresh 300s cap; no carryover. No
independent review was available. All writes stopped; unrelated worktree changes
were preserved.
