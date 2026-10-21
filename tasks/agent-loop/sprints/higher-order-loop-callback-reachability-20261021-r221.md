# R221 — Higher-order loop callback reachability

Status: CLOSED, bounded candidate-only source/native outcome C; Luna solo
primary, no independent review.
Baseline: `4a4450f33cafb5246b95958f1b1a2af8eb510c10` on
`research/simple-sub-intrusion`.

## Parent and exact source question

Continue the original computation-forwarding preservation theorem and R71
source-reachability/required-fiber obligation. R218-R220 traced the fixed and
repeated helper sources; no third-owner merge plus later Work::Bound copy of
the loop slot-4 item arose. This packet checks whether passing the retained
`loop` as a higher-order callback to a function that calls its formal twice
creates that consumer path.

Use one ordinary source containing R72's unchanged `loop`, `direct`, and
`helper` definitions, plus:

```yu
my repeat (f:[io] int -> int) (z:[io] int) = {
    my first = f z
    f z
}
repeat loop q
```

Run public ordinary `CandidateInference::solve(hir)`. Record constructor
admission, exact slot-4 source/physical owner, callback formal and both Apply
occurrences, Local/FreshUse mapping, complete Work::Bound owner/consumer trace,
and complete intrusion-forest history/replay. Outcome C is source-specific and
only applies if this accepted source's complete relevant trace lacks the
requested pattern. An authentic earliest source-constructor rejection is B
for this exact source. Do not infer a general impossibility or parent closure.

## Exact write paths and checks

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract
- `notes/theory/2026-10-21-r221-higher-order-loop-callback-reachability.md`
- `tasks/agent-loop/current.json`

Add one focused test and use existing test-only R148 traces and read-only
retained route/lineage accessors. Do not add instrumentation, alter semantics,
modify samples, or change expected outputs. Run the focused test first; if the
source is admitted and the trace is interpretable, run the ordinary
`yu-playground` package suite. Finish with sprint-state check, tooling unittests,
`git diff --check`, byte limit, explicit-path commit and push. 600 seconds, no
carryover. Solo primary; no independent review claimed.

R71, global R72, original theorem and production gates remain OPEN in every
outcome.

The exact result is recorded at
`notes/theory/2026-10-21-r221-higher-order-loop-callback-reachability.md`.
The callback creates a genuine Work::Bound copy for its own formal item, but
the complete source/alias trace keeps that item separate from the loop
slot-4 item; no requested merge-then-copy path occurs in this case.
