# R19 revision 3 — bounded runtime-lineage repair

Parent and theorem unchanged: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`,
OPEN/closure0, original source/native domain and quantifiers intact.

Base contract revision 1 SHA-256
`75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.
Read-dependency revision 2 SHA-256
`ac088984d5303421091a203f63699ba212ed2bf01b90daa80fbc1f797f83317d`.
This revision adds no source or solver write authority. The proof/source results
and their CLEAN reviews remain at commits `6748039fa` and `118375dce`.

## Reviewed runtime target and exact repairs

Preserve the original frozen R19 runtime snapshot, handoff and BLOCKING review.
Snapshot pins:

```text
eb7f80345ac938fad671bae5ac6cedc1d9da94dbdf1d9bd0df193aaa2dfd3956 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
7f59ba693829c7568c057450ccdde77b768466033b668e8199fc19b7c07339e1 tools/inference-playground/tests/runtime_resume.rs
a7c14f5a704f580f1f9c2b136b4303b09ff144a29f13c23f4c8653a69d9458fa tasks/agent-loop/inbox/20261018-operation-v1-local-binding-runtime.md
```

The same stopped R19 implementer may resume only these exact paths:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/tests/runtime_resume.rs`
- new handoff `tasks/agent-loop/inbox/20261018-operation-v1-local-binding-runtime-r2.md`

Repair the three reviewed findings together:

1. Keep R18's direct catch-result Apply route. For a local-binding route, derive
   the response invocation only from the source-authenticated chain
   initializer Catch -> exact binding -> resolved Name -> its actual g Apply.
   Never make Name generally transparent or infer identity from spelling/type.
2. In that local route, the actual g Apply may also be the response-closure
   invocation. Keep it distinct from the `k response` continuation Apply and
   callback-body operation Apply; do not demand two different invocation owners
   for the same actual call. Preserve exact closure handle/environment checks,
   callback request owner, live outer arm, and all R18 direct-path requirements.
3. Replace the malformed sibling negative control with balanced accepted source.
   The test must first establish parse/HIR and unchanged static candidate
   acceptance with the existing receipt. It must then fail at the precise
   sibling binder/cell lineage check. Parse rejection cannot satisfy it.

No solver or source semantic rule changes, receipt schema changes, casts,
provenance shortcuts, expected-output changes, or FieldBound/FreshUse claims.
If unchanged static candidate acceptance fails, record the earliest exact
boundary in the handoff and leave local-runtime success NOT_RUN/failed; do not
rewrite source or solver rules.

## Review, verification, and resource delta

The same independent `compiler_referee` who found the three blockers reviews
the frozen repair as a delta against that report and the unchanged R18 path.
All three findings must close before the focused target runs. No test, build or
formatter runs before this CLEAN delta review.

After CLEAN, Luna runs only:

```text
cargo test -p yu-playground --test runtime_resume
```

The target must show successful same-HIR local-g lineage and a valid-source
sibling-binder/cell negative control. Luna integrates the exact approved paths
and updates the handoff/current state after verification.

The prior R19 grant remains fully charged at 2400/2400 seconds. Add exactly
900 seconds, bringing the R19 cap to 3300 seconds, allocated as:

- runtime repair: 360 seconds;
- same reviewer's independent delta review: 240 seconds;
- one focused test run and integration: 300 seconds.

No old allocation is reset or carried over. Astra remains 0. Stop on target
completion, this added cap, or any need to change solver/source semantics or
receipt schema. PREFIX-1/USE-1 remains a later sprint; the runtime result does
not establish native FieldBound transport or close a parent condition.
