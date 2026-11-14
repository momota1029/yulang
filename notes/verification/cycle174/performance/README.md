# Certificate performance smoke tests

These are runtime experiments, not theorems and not Checked source programs.
`tools/BenchCycle174.lean` builds synthetic role-chain Registry values, with or
without duplicated outgoing clauses, and evaluates only `certify`. Valid source
language declarations are not claimed. Timings include printing and are coarse.

Small matrix: lengths 4, 8, 12, each with and without duplicate edges, all
returned true; exit 0. Observed elapsed milliseconds (single run):

|length|no duplicates|duplicates|
|---|---:|---:|
|4|1|0|
|8|1|7|
|12|1|148|

Two larger batches did not finish within their caps:
- original all-pairs lengths 4,8,12,16,20: timeout 60 seconds, exit 124;
- follow-up 16/duplicated,20/nonduplicated,20/duplicated: timeout 45 seconds,
  exit 124. Buffered command output was not retained before termination, so
  no individual unfinished case or per-case timing is inferred from this batch.

The first benchmark elaboration attempt also exited 1 because the IO monad
was inferred as BaseIO; explicit IO Unit fixed it. Its diagnostic is preserved.
No theorem source changed as a result of these experiments.

The current producer is executable but recomputes overlapping height subtrees;
no efficient complexity bound has been proved. Memoized/deduplicated graph
analysis would be needed before treating it as a scalable compiler component.
The formal certificate soundness/completeness and all focused proof audits
remain PASS independently of these runtime limits.
