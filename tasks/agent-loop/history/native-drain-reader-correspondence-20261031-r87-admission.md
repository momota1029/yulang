# R87 admission

Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`
Contract SHA-256: `fb57b17b311afb459dd3aea20819ae902955651862c4e401729189dc3e0a5314`
Input manifest SHA-256: `c96e2ada0461e0ed5527af4c4d96e697034aa9428420f56c10b6d489825409f4`
Baseline: R86 closeout checkpoint on `yulang3`.

R86 is closed as `FAILED_AUDIT_CAP_EXHAUSTED`; its frozen outcome is
`tasks/agent-loop/history/native-receipt-join-20261031-r86-outcome.md` (SHA-256 `a25297863fc2320f3a7557f98628ee51623d41a089749fbb78a2b8b95e36bc4f`). The seven failed declarations remain unaccepted.
R87 starts a different proof method under the unchanged user goal, with the
three actual readers modeled separately. R86's failed declarations are not
permitted as imports.

Admitted envelope: 3,600 seconds total; proof 1,400; read-only source proposal
1,000; independent review 700; primary 500; Astra 0. At most two separately
authorized, independently reviewed in-memory Lean stdin calls at 120 seconds
each, 240 seconds total. No source edits, Rust/Lake/Cargo/build/test execution,
cache, target, scratch, environment, worktree, nested CLI or service.

Exact leases are recorded in the manifest. This admission authorizes bounded
proof/source/review work only. A Lean execution still needs a frozen candidate,
exact input hash, fresh pre-execution review, and its own committed/pushed
authorization. Luna retains exclusive state, staging, commit and push authority.
