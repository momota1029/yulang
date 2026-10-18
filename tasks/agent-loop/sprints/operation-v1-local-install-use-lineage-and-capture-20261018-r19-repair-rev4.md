# R19 revision 4 — test-only runtime-lineage repair

Parent and theorem unchanged: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`,
OPEN/closure0, original source/native domain and quantifiers intact.

Base contract rev1 SHA-256
`75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.
Read-dependency rev2 SHA-256
`ac088984d5303421091a203f63699ba212ed2bf01b90daa80fbc1f797f83317d`.
Runtime repair rev3 SHA-256
`9002cc81daf3a6bde262fcf8390dfdc6a48f6145106327fb00236ed9f38b6cfe`.
This revision adds no solver, source, or runtime implementation write authority.

## Frozen rev3 evidence

The rev3 runtime implementation is frozen at:

```text
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
679c21fb6810b636791374ddeff19b131952e53567533f6f48d7d7dae9187a8b tools/inference-playground/tests/runtime_resume.rs
4444f9b8b0117db2f2fcac7cc20875c1c6630d475baa99375d647facfec1581f tasks/agent-loop/inbox/20261018-operation-v1-local-binding-runtime-r2.md
```

The same compiler referee's rev3 delta review was BLOCKING only on two test-file
findings; it found the local invocation join and preserved R18 direct path
structurally repaired:

1. The sibling source replacement still removes the initializer Catch's closing
   brace, leaving malformed source. Keep the Catch close and retain assertions
   for parse/HIR plus unchanged static candidate acceptance before checking the
   sibling binder/cell lineage rejection.
2. The test matches `sibling_result` by value, partially moving its `String`,
   then borrows it for the assertion message. Match by reference or bind the
   error by reference so the subsequent diagnostic remains valid.

## Exact authority and review gate

The stopped R19 implementer may write only:

- `tools/inference-playground/tests/runtime_resume.rs`
- new handoff `tasks/agent-loop/inbox/20261018-operation-v1-local-binding-runtime-r3.md`

`program.rs` and `machine.rs` stay frozen at the hashes above. No solver/source
rule, runtime implementation, receipt schema, expected-output, or test-gate
weakening is authorized. The accepted-source sibling test must first prove
parse/HIR and unchanged static receipt acceptance; it must then reject only at
the exact sibling binder/cell lineage boundary. If static acceptance fails,
record the earliest boundary and leave runtime behavior NOT_RUN/failed.

The same independent compiler referee reviews the frozen test-only delta,
including exact pins and both findings. No test, build, or formatter before a
CLEAN review. After CLEAN, Luna runs exactly once:

```text
cargo test -p yu-playground --test runtime_resume
```

No retries on changed bytes without a newly authorized reviewed target.

## Resource delta and stop

The prior R19 cap of 3300 seconds remains fully charged and unchanged. Add exactly
600 seconds, bringing the R19 cap to 3900 seconds, allocated as:

- test-only repair: 120 seconds;
- same reviewer's delta review: 180 seconds;
- one focused test run and integration: 300 seconds.

The full grant is reserved/charged at issue; no carryover or reset. Astra 0.
Stop when the focused target completes, the added cap is reached, or another
owner/semantic/runtime change is required. PREFIX-1/USE-1 remains a later
sprint. This test/runtime result does not establish native FieldBound transport
or close any original parent condition.
