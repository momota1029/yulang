# R114 rev4 prospective spec review transcript

Reviewer: `/root/r128_recovery_spec`, fresh read-only review. Luna records this
transcript because the reviewer did not write files.

Frozen target: `tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev4.md`,
SHA-256 `b42ac475a6e5049edd89f7ba3eda91933af61ae43324821c3cc65e8c19b30c6e`.

Result: **CLEAN prospective review**. The split preserves the original finite
observation through composition: the crate unit test checks direct Machine
`HandlerEvidence(site)` against the exact public `execute` error; pinned
`main.rs` propagates that error unchanged to stderr with a newline and failure
status; the integration test separately checks stdin execution, failure,
empty stdout, and diagnostic category. This changes harness coverage, not the
semantic expectation.

Exact leases and private API boundaries are explicit. Prospective CLEAN
precedes edits; frozen outputs and three final CLEAN reviews precede both
serial commands. The library substring filter targets the prescribed unique
test; the integration command retains `--exact`.

Accounting is coherent: `2,221 + 840 = 3,061`; rev3's `2,340 - 2,221 = 119`
seconds are reallocated once, yielding a 721-second cap increase. Historical
compile failure and all parent gates remain preserved.

No writes, tests, builds, compiler/CLI invocations, formatter, or Git operations
were performed by the reviewer.
