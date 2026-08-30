# Performance policy

Performance is a design property, not a cleanup pass.

## Hot paths

Treat these as hot or potentially hot unless measurement shows otherwise:

- parsing and CST/AST transitions;
- lowering;
- inference and constraint processing;
- normalization and simplification;
- name resolution and scope lookup;
- diagnostics preparation;
- worklists, caches, and incremental invalidation;
- backend transforms over whole modules or functions.

## Avoid hidden work multiplication

Do not introduce:

- repeated calculation of the same fact in multiple phases;
- CST/AST rescans to recover information the owning phase could carry;
- large unnecessary clones;
- per-entrypoint reconstruction of the same table, map, or index;
- cache/invalidation schemes before their authority and rollback are clear;
- inner-loop allocations, hash-set construction, linear cross-checks, or branches without accounting for call volume;
- the assumption that a later cache will make an unclear algorithm acceptable.

Build the smallest clear kernel based on a known algorithm or explicit invariant, then extend it.

## Performance-review risk trigger

Every producer accounts for obvious work added by the diff. A separate
`performance_auditor` is mandatory only when at least one of the following is
plausibly material:

- asymptotic complexity changes;
- a new or expanded traversal on a hot path;
- nontrivial allocation/clone volume at realistic call frequency;
- cache, memoization, invalidation, table/index/worklist reconstruction;
- inner-loop work whose aggregate cost is uncertain;
- recursive/parallel/locking/thread-count behavior;
- benchmark-motivated implementation claims;
- a verification command capable of high memory, long runtime, or process explosion.

An incidental branch, small local allocation, or bounded traversal does not
alone require a separate auditor. The implementer still reports its expected
cost. Escalate when scale or call frequency makes the effect material or
unknown.

## Measurement decision

Do not benchmark by default. First answer:

1. what semantic work unit may have changed;
2. whether static complexity/call-frequency analysis resolves the risk;
3. what decision a timing measurement will change;
4. what representative input exposes that decision.

If no concrete decision depends on timing, do not collect repeated timings.

## Ordinary measurement budget

For an ordinary M1/M2 task:

1. prefer a harness that compares baseline and candidate in one invocation;
2. use one warm-up and three paired measured samples at one representative
   input size;
3. record median and range (or equivalent robust summary), not only the best run;
4. stop when the evidence is sufficient to classify the change as a material
   regression, material improvement, or no detected material difference within
   the observed noise.

The ordinary hard budget is:

- at most **8 benchmark process invocations** total;
- at most **10 minutes wall time** total.

A paired sample collected inside one benchmark process counts as one process
invocation. If baseline and candidate require separate processes, three pairs
normally consume six measured invocations; remaining budget covers warm-up or
one diagnostic rerun.

Do not automatically multiply repetitions by every input size, backend,
feature flag, and build mode. Add one dimension at a time only when the previous
result leaves the decision unresolved.

## Adaptive extension

If three paired samples are inconclusive because observed variation is large or
the median difference is within roughly ten percent, choose one of:

- report that the result is inconclusive within the ordinary budget;
- improve the harness or input isolation;
- extend to five paired samples when this fits within the same process budget;
- request a larger experiment.

Any plan above 8 process invocations or 10 minutes requires an explicit written
justification from `performance_auditor` and primary approval before execution.
A plan above 16 process invocations or 20 minutes requires user approval.
Twenty-four separate measurements are therefore never a default regression
check.

Use multiple input sizes only for an asymptotic claim. State the sizes and why
they distinguish the candidate complexities before running them.

## Evidence report

A performance report identifies:

- semantic work unit and expected complexity;
- environment/build mode;
- exact command/harness;
- warm-up and measured sample counts;
- input size(s);
- median/range or another robust summary;
- process-invocation and wall-time budget consumed;
- conclusion and what remains unresolved.

Publication-grade statistical certainty is not required for an ordinary
regression guard. Honest bounded evidence is preferable to a large, unexplained
measurement table.

## Resource safety

Do not run an unscoped or unfamiliar heavy suite merely to be thorough. Establish the current test inventory and expected resource profile first. Historical yulang2 incidents are recorded under `notes/incidents/`; their old skip lists are not current yulang3 policy.
