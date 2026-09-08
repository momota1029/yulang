# Source-root statement topology

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the explicit request to reconstruct parser
responsibilities rather than mechanically rename temporary paths.
Reviewed-by: scoped read-only root topology audit.

Scope: behavior-preserving extraction of source-root statement progression from
`source_file.rs` into `root_statement.rs`. The new owner receives the existing
root progression state (`leading_header`, pending Item, origin, LineEntry,
separator state, and previous statement context), performs root statement
dispatch, operator body handling, root recovery, and continuation, and returns
the same result to the host facade. `source_file.rs` remains the source-root
facade: `RootCandidate`, `Recover`/`CstOutput` construction, Root node open and
finish, frozen header reconciliation scope, and source/header identity.

Authority: user-directed responsibility reconstruction,
`2026-09-09-syntax-phase-topology.md`, and
`2026-09-05-yumark-parsed-yulang-fence-addendum.md` §§3--5/§7. This is only
Phase A of the later Yumark construction path; it creates no cell entrypoint.

Header reconciliation stays concrete inside source-root progression. Its
`leading_header && physical_start` decision, semicolon/layout handling,
pending child exits, and first non-header transition determine shared frozen
record order, so it must not become an outer pre-pass or an inferred generic
mode. `header.rs` remains source-leading discovery and opaque header scanning.

Do not add a generic `parser`/`root` umbrella, a public API, a cell-mode
fallback, or a new mode flag. Do not alter CST, accepted syntax, recovery
records/order, frozen reconciliation, Item/leading/origin/LineEntry handoff,
operator-table use, root Error behavior, or tests. In particular, this phase
does not change the existing abstract-boundary assertion or the opaque Root
Error `finish_opaque_opener` path: fence-boundary termination and no-copy
opaque recovery are separate bounded gates before any Yumark cell owner.

Before closure run root/header/full-parse/public-boundary and focused recovery
controls, package check, format, and diff. Measurement budget: zero
samples/processes.

Construction completed 2026-09-09. M2 topology preflight and independent
delta review found no defect. Root/header/full-parse/public-boundary/recovery
controls passed 63 tests with one existing manual measurement harness ignored;
package check, format, and diff passed. Benchmark use: zero samples/processes.
