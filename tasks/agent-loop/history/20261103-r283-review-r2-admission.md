# R283-R2 clean review admission

The `/root/r272_goal_dispatch` selector recommends one corrected independent
review before another Sol trial. R283-R1 is preserved as INCOMPLETE with the
full 450s charge. Its contract-only identity/hash gate passed. After GO, the
reviewer's first technical command failed because `python` was unavailable;
the `python3` retry resolved filename-only config pins from repository root and
reported a false `lean-toolchain` mismatch. It stopped without viewing
technical content; actual byte mismatch was not established. No mathematical
disposition follows.

R283-R2 adds 600s: independent Sol reviewer up to 450s and Luna up to 150s for
preflight, gates and adjudication. All prior allocations and charges remain;
cumulative allocated envelope is 4,200s. No proof producer grant is issued.

## Explicit input manifest and Luna preflight

`tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2-inputs.json`
is frozen at SHA-256
`1a6f485ba1e48dc0b351d644d32803a70cbe485aa5793538ab811cc732b409e5`.
It lists exactly 16 repository-relative paths: 11 workspace modules under
`notes/theory/lean/YulangClosure/`, three configs under
`notes/theory/lean/`, and the frozen candidate module and handoff. Luna's
`python3` preflight hashed each exact listed path and produced MATCH for all
16. No input body was printed. The explicit paths remove the filename-only
resolution ambiguity. The candidate and handoff remain frozen at the R283
pins; the `.lake/build` lease remains frozen and untouched.

Review contract
`tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2.md` is pinned
at SHA-256 `aa72f665f4d2f99746fdf764a758824ac69c246f21b67f9448378b3baef17ecf`. Fresh identity is
`/root/r283_counterexample_clean_review_r2`, registered
`parent_edge_auditor` with profile-fixed Sol role. Reviewer is read-only, has
450s, no descendants and no output-file lease. Follow contract-only WAITING,
Luna GO, one hash-only first technical operation over the manifest and all 16
pins, then source-first inspection of `incomingJobs`, `copiedRow`, `step`,
`runPrefix`, followed by candidate/handoff. Stop on any actual mismatch. No
checker rerun, build/cache, Rust, source, Cargo, tests, probes, external bodies,
Git or writes.

Luna owns the R2 history receipt, adjudication and current-state synchronization.
Parent/A/B remains 0->0; R70 and source/native correspondence stay open;
implementation remains NO_SAFE_CODE_SLICE. The result may assess only the
counterexample to this particular `RowsValid` predicate, not Rust reachability,
R70 W or stronger-invariant impossibility. No capture-closed proof is admitted.
