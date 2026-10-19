# R120 implementation handoff — rev1

Sprint / contract: local-resumption-cli-20261019-r120, rev2, SHA-256
`6af7d6ad17684de717742586baa3d504adc73da6a37b8ba511b59a2ca327ff68`.
Assignment: R120 implementation, handoff revision 1. Baseline: `af551a720`.
Worker `/root/r118_implementation_lane`; current session
`current-conversation-2026-10-19-breadth-surface-method-goal`. Launch receipt:
current-session R120 assignment message; effective model/effort UNKNOWN.
Parent: finite continuation/resumption hygiene witness and early runnable
effectful source evidence. This is one test-only public CLI observation; it
does not prove the general Resume parent or any source/native theorem.

## Frozen test artifact

Added only `tools/inference-playground/tests/cli_local_resume.rs`.
Written-file SHA-256, including its final LF:
`c315daccfd28279192b0052f55c5558fa11133509291855129f744037633e747`.
The exact two leased output paths are this test and
`tasks/agent-loop/inbox/20261019-r120-implementation.md`; both have one author
and no contributing descendants.

The test uses the exact source below, 175 UTF-8 bytes with no final LF, SHA-256
`7f3e39f4eb59da052e209bae88cd80cedff00e7158d0818e8b02c5faa70ee25f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 9 }
my main = relay { my result = io::tick 7; result }
```

It launches `CARGO_BIN_EXE_yu-playground` with exactly
`--run main --steps 10000 -`, writes the source to child stdin, and asserts a
successful exit, stdout exactly `9\n`, and empty stderr. The test has not run;
these are its frozen expectations, not an observed result.

## Parent/source correspondence and boundaries

The unchanged `runtime_resume.rs` test
`raw_response_enters_the_hole_under_the_still_active_containing_owner` uses
the same source and asserts direct-machine integer `9`. The new test adds a
public stdin path only. `main.rs` dispatches `--run main` to `execute`; the
public `execute` path prepares one HIR, obtains candidate inference, constructs
RuntimeProgram from that HIR, runs the requested definition, and prints the
completed integer with LF. This test would observe that public path if it
passes. It does not inspect internal event, binder, environment, or continuation
identity and cannot establish the proof trace by output alone.

The required finite proof still distinguishes response `9` from the pending
`result` local and final result: capture the current continuation, apply raw
`k 9`, resume the saved body under its original lexical environment, complete
the local binding, look up that original binder, finish `main`, and project the
public value. The source/candidate admission, same-HIR join, original request
and continuation/environment identity, active containing owner, and bounded
completion remain conditional proof premises. Do not infer a general
continuation, foreign-owner, permission, evaluator, or Simple-sub/A-B theorem.

## Evidence reused and exclusions

- The R120 contract's exact-source pin and the unchanged direct-machine
  `runtime_resume.rs` assertion supply the finite source/value target.
- R111's one-shot failure and `cli_raw_resume.rs` remain unchanged. Its two
  CLI recipes are distinct from this 175-byte source; this test does not repair
  or retry R111.
- Runtime/receiving authority is charter §§14–17 and 21, subject to §24's
  receiver-role boundary. R120 makes no method/role or semantic adoption.
- The public cell is finite executable evidence only after Luna's authorized
  one-shot Cargo test and the required three CLEAN reviews. No proof premise is
  discharged by authoring this test.

## Pins, checks, and stop receipt

Contract direct pins include `runtime_resume.rs`
`449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580`,
RuntimeProgram `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca`,
machine `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`,
continuation `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`,
and receiving `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`.
The governing charter pin is
`547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`.

No production code, existing test, old expectation, runtime diagnostic,
question, or other path changed. No Cargo/build/test/CLI/Git command or probe
ran. Read-only contract, history, and source-test inspection plus in-session
hashing only; authorized verification remains NOT_RUN pending all three fresh
CLEAN post-output reviews. No scratch/generated paths.

Mutual TODO `R120-IMPL-PROOF-1` — proof owner `/root/r118_proof_lane`: connect
the exact source's pending `result` local and request to the captured raw
continuation, show `k 9` resumes through that saved body and original lexical
environment under the still-active containing owner, then identify the resumed
local lookup and final public integer. Falsifiers: another binder/environment,
expired/replaced owner, reinstalled selected shallow handler, skipped saved
body, failed preparation, or public status/value/streams differing from the
contract. Evidence request only; no additional path or authority is granted.

Requested model/effort: Luna/high. Effective observed model/effort: UNKNOWN.
Worker: `/root/r118_implementation_lane`; no descendants. Exact elapsed seconds,
CPU and memory are unavailable; active work stayed within the 300-second cap
and no executable resources were used. All assigned writes are frozen and
stopped; fresh compiler/source, spec, and regression reviews plus Luna's
one-shot verification remain pending.
