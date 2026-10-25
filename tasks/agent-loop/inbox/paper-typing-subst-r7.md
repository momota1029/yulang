# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r7 — frozen failed construction

Outcome: `FAILED_CHECK`; no new theorem accepted. Parent theorem and downstream
inference/executor/A-B claims remain OPEN. Primary-only writer: `/root`.
Contract: `tasks/agent-loop/sprints/paper-execution-typing-r7.md`, SHA-256
`4eb7ed19c8d0ef3f765a4b9dff50baeafa74ae52cf470d228346d44d721a95ec`.
Baseline: `ee689474d4c77b176ce445483736753e4f58ace2`; branch
`research/simple-sub-intrusion`. No source/native or independent review was run.

## Scope and artifact

R7 carried the R6 candidate record rules into the primary checkout: `RecordShape`,
`RecordField`, `RecordPayloadsTyped`, record introduction, required-only `field`,
and declared-label `lookup` returning `1 ∨ A`. It retained required-label
inclusion, actual-label uniqueness, and per-payload typing, without requiring
optional fields or correlating the raw Presence tag with the declared row.
The raw record map helper and `List.attach_map_val` were added to the attempted
substitution case. These are unverified candidates, not accepted evidence.

The five-motive recursor declaration and pinned `List.attach_map_val` type were
inspected under Lean 4.35.0. The requested proof was not successfully delivered.
The proof module retains the R6 case-based mutual theorem block; it does not
satisfy the R7 explicit-recursion success condition.

## Attempts and diagnostics

R7 had four Lean/Lake invocations before the two focused builds (6/8 total;
approximately 17.8 checker seconds observed). One final read-only Lean stdin
invocation inspected the generated recursor and tested the exact mapped-record
equality, for 7/8 total. It confirmed that `PaperValueTyped.rec` exposes all five
mutual motives and that the concrete `List.attach_map_val` instance lifts through
`Value.record` with `congrArg`; `#print axioms PaperValueTyped.rec` reported no
axioms. This was not a substitution theorem proof. The failed builds were:

1. Changing `RecordPayloadsTyped`'s environment from an index to a parameter
   caused `PaperExecutionSyntax` to fail: all mutual inductives must have the
   same number of parameters, while `ValuesTyped` and `RecordPayloadsTyped`
   then had different parameter counts. This architecture was reverted.
2. With the original environment index restored, `PaperExecutionSyntax` built,
   but `PaperExecutionTypingSubstitution` still failed. The kernel application
   mismatch at `RecordPayloadsTyped.subst` remained: the recursive IH's
   environment index did not match the derivation's environment index. The
   record case also remained unable to identify `fields.attach.map` with
   `fields.map`, even with `List.attach_map_val` in the simp set.

The R6 diagnostic and axiom-audit record remains at
`tasks/agent-loop/inbox/paper-typing-subst-r6.md`. No successful R7 typing
module build or R7 theorem axiom audit exists. No `sorry`, `admit`, project
axiom, or failed declaration is claimed as proof. No source file was discarded;
the attempted candidate remains available for the next bounded repair.

## Accounting and next boundary

R7 used 6/8 Lean/Lake invocations and stayed below its 120 checker-second and
900-second limits. Static `python3 tools/agent_sprint.py check` and
`git diff --check` passed; these do not establish Lean proof validity or
independent review. No tests, Rust/native builds, or compiler implementation
changes were made. R6 remains `FAILED_CHECK`; R5's prior partial checked result
remains the only checked theorem slice. Fresh review is `NOT_RUN` and no safe
reviewer slot was established; all eight unknown legacy/foreign reservations
remain quarantined.

Next bounded action is to isolate the environment-index mismatch and apply the
actual five-motive recursor to the proof, rather than retaining the current
mutual `cases`/recursive-theorem block. Preserve the original full substitution
theorem and exact record/source distinctions, and audit every resulting theorem
before claiming any success. The paper-to-Rust field/lookup correspondence remains OPEN.
