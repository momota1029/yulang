# Native routing for computation formals

Date: 2026-10-15
Status: implemented and independently reviewed local routing slice; handler removal and full hygiene remain OPEN
Baseline: `261605657dbcd391d87b7eaa2c68b2a59349fa47`
Branch: `research/simple-sub-intrusion`+
## Authority and construction

The user requested implementation and proof, including `thunk: [signal] int`.
The source role is already selected by the SCC/intrusion charter section 21;
annotation-effect-hygiene-integration section 1.1 fixes the signal handling
expectation and permits an additional write effect. This change implements
the argument route needed by that expectation, not the handler consumer.

`candidate_call.rs` retains Value/Computation role on the source formal.
`candidate_source.rs` preallocates an entry row only for Computation formals,
at their parameter level. Each Computation Name carries that same row through
ordinary bidirectional effect constraints. `candidate_effect.rs` constructs
the root value annotation separately; the outer concrete effect annotation
does not impose a closed input cap. Its original source annotation remains
available for the later permission consumer. A singleton symbolic annotation
is linked to the entry row.

`lib.rs::admit_lambda_fact` uses that entry as Function ArgumentEffect and
omits unconditional entry-to-return forcing for Computation parameters.
Their body carries effects when the parameter is used. Value parameters keep
their original lazy entry allocation, mandatory entry forcing, and pure Name
lookup. Two legacy Lambda constructors in `shadow_apply.rs` explicitly retain
their unregistered path.

Cost: constant metadata per formal/recipe; two ordinary constraints per
Computation Name and per singleton symbolic root annotation. No new graph
search or extra Value entry allocation is introduced.

## Review and checks

M2, one independent `compiler_referee` (`review_computation_route`). The
review covered constructors, annotation variance, levels, Function ports,
capture/generalization and immediate consumers. Its minor allocation-contract
finding was repaired by restricting preallocation to Computation; no existing
test expectation changed. Delta review found no remaining findings.

Two serialized invocations of
`CARGO_BUILD_JOBS=2 timeout 300s cargo build -q -p yu-playground` passed without
warnings. Fourteen bounded direct CLI executions (30-second cap each) are
retained in `/tmp/yulang-computation-route-85zlnid9`:

- Spaced annotated `relay (thunk: [signal] int)` with Catch solves.
- An unused Computation argument permits an empty-effect result.
- Using that Computation argument conflicts with an empty-effect result.
- The unused Value counterpart still conflicts with an empty-effect result.
- The existing callback-block fixture still solves with pure final Name lookup.
- Exact adjacent headers such as `relay(thunk: ...)` remain unsupported at
  the earlier HIR header owner. A separate HIR slice is required.
- The additional-write source used a unit formal `both()` / `both ()`, which
  is unsupported by the current named-parameter HIR carrier. Those runs do
  not establish the extra-effect expectation.

The CLI observes inference; it does not execute a runtime return value.
Catch still forwards its whole scrutinee effect, so solving the annotated
example does not establish that it returns `1` or removes signal.
Whitespace checks passed. No tests were added or run, no broad suite was run,
and no benchmark processes or samples were consumed. Broad compilation is
deferred to the coherent phase boundary.

## Remaining work

Connect local annotation permission and operation-aware Catch subtraction;
finish scoped compose release and its source/FreshUse/late-replay proof.
The original full source hygiene, soundness, principality and production
gates remain OPEN. This local review does not certify those conclusions.
