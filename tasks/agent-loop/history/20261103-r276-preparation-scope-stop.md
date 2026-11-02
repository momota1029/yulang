# R276 preparation STOP — out-of-inventory manifest exposure

R276 was not admitted and no Sol assignment or GO occurred. During Luna's
preparation, one command used a shell glob over workspace Cargo manifests
instead of deriving every search path from the pinned 229-entry inventory.
Its output displayed feature/dependency configuration lines from these paths:

- `tools/inference-playground/Cargo.toml`
- `tools/inline-authentic-extraction/Cargo.toml`
- `tools/bench-runner/Cargo.toml`

A subsequent metadata check against the pinned inventory found these three
paths are outside its 229 entries. Their displayed contents are excluded from
evidence and will not be used to establish a production route. No source code,
test body, build, probe, test, output write or production edit occurred. The
issue is a Luna preparation read-scope breach; stop further source exploration
under this unadmitted packet until the path authority/boundary is reconciled.

Prior R275 remains CLOSED INCOMPLETE per
`tasks/agent-loop/history/20261103-r275-production-entry-unresolved-milestone.md`.
No new work was charged to Sol. Unknown workers, quarantined paths and all
unrelated leases remain unchanged. The full inference/effects, R70/R71,
Need_D, Parent/A/B and implementation statuses are unchanged.
