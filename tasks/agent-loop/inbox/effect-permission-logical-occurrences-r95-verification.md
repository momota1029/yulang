# R95 primary execution authorization and verification receipt

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R95`.
This file is Luna's primary-owned exact execution authorization. It is effective
only after the commit containing these bytes is pushed to `origin/yulang3`.

## Pushed pre-execution authorization

Independent exact-input review: **PASS**, frozen at
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`,
SHA-256 `9b694c2c29ab4c3b88cfd456862ce101f5249d72cfa5cbee83d477ae1aa890a0`.
Reviewer measured 20 seconds of the 60-second grant. Its exact reconstructed
input is 106,897 bytes, SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.
The R93 candidate remains SHA-256
`3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192`.

I authorize exactly one Lean invocation, only after this receipt is pushed:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024
```

The reviewed stdin is assembled in memory from the three manifest-pinned source
files, no separator bytes, with only the two reviewed inter-module import lines
removed. No output file, scratch, cache, Lake build, test, project copy,
worktree, or environment is authorized. One Lean process only, capped at 120
seconds and 1,024 MiB. This receipt authorizes no repair or second call.

Primary authorization timestamp (UTC): 2026-10-31 16:55:31 UTC.
Authorization commit: the commit containing this receipt must be pushed before execution.
Lean execution status: **NOT RUN**.

## Execution result

To be filled by Luna only after verifying that the authorization commit reached
`origin/yulang3`. Record UTC start/stop, exact exit status, elapsed time, peak
RSS, complete stdout/stderr, all ten elaborated theorem types and all ten
complete axiom reports. If the invocation errors, times out, or exceeds any
limit, preserve the exact diagnostic and do not retry.

## Independent result review

Pending. The independent result reviewer receives this frozen authorization
and the complete execution output. The result remains a candidate until that
review and Luna's adjudication; source/native and original parent gates remain
OPEN.
