# LEAN-CALL-STEP-TYPING-20261025/r2 — repair of dependent case bindings

Status: **FROZEN**, Luna primary. Baseline commit: `862c8777684587f6ca2b20d22859f954804a2c50`; branch `research/simple-sub-intrusion`.

## Exact proposition — unchanged from r1

In `YulangClosure.Control`, prove:

```lean
theorem call_state_typed_step_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hstep : CallControlStep md s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix
```

This remains conditional one-step preservation for the existing `CallControlStep` relation and existing `CallStateTyped` judgment. It establishes no progress or successor coverage, and no world, CallView, scope/view-context, receipt, effect, source/native, original A/B, inference A/B, or production result. The typed `.force (.view (.delay body) occurrence)` gap remains OPEN. r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`.

## r1 failure and repair hypothesis

r1 candidate `notes/theory/lean/YulangClosure/CallStepTyping.lean` SHA-256 `4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab` failed against pinned modules with six unknown pattern-field identifiers: `consumer` at lines 89 and 94; `effectView`/`resultView` at lines 131 and 208. The exact failure is frozen at `tasks/agent-loop/sprints/call-step-typing-20261025-r1-outcome.md` SHA-256 `d7606d506a52be722e4504cce91eee1b76c73df14659b3b67eb6b2b4f4dfa158`, and in r1 verification JSONL SHA-256 `6c0737f3b825f704a2f5298953bc37b9d92fe1fd7bc3e1e2c7a77be6dc3a85df`.

Fresh r2 author may use the frozen r1 candidate only as read-only source. In the new module, bind indexed constructor fields explicitly in the affected transition cases or let the expected target infer them. Audit all dependent cases for the same scope issue. Preserve the exact consumer, both view fields, transition substitution, response-binder lifting, all 28 cases, and the unchanged theorem. Do not import the failed r1 module. Any need to change proposition, dependencies, source semantics, or add a premise stops r2 and returns the exact obstruction.

## Exact leases

Author writes only:

- `notes/theory/lean/YulangClosure/CallStepTypingRepair.lean`
- `tasks/agent-loop/inbox/20261025-call-step-typing-r2.md`

Luna owns:

- `tasks/agent-loop/inbox/20261025-call-step-typing-r2-verification.jsonl`
- `notes/theory/lean/.lake/call-step-typing-r2-check.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.ilean`
- `tasks/agent-loop/inbox/20261025-call-step-typing-r2-review.md`
- `tasks/agent-loop/sprints/call-step-typing-20261025-r2-outcome.md`

All author paths and Luna query/output/review/outcome paths were absent before r2 admission. The author freezes exact source/handoff hashes and STOPs before any Lean invocation. Luna compiles the candidate once, and only on success queries the exact theorem signature and axioms once. Stop on first error/mismatch; no automatic repair retry. After both successes, assign one fresh nonauthor `compiler_referee` review of the frozen candidate and complete receipts. CLEAN review plus Luna adjudication is required for acceptance.

## Frozen source pins

| Input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `notes/theory/lean/YulangClosure/CallEntrySpineComposition.lean` | `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| r1 candidate `CallStepTyping.lean` | `4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab` |
| r1 outcome | `d7606d506a52be722e4504cce91eee1b76c73df14659b3b67eb6b2b4f4dfa158` |
| r1 complete verification JSONL | `6c0737f3b825f704a2f5298953bc37b9d92fe1fd7bc3e1e2c7a77be6dc3a85df` |

Reuse only these accepted prebuilt outputs after Luna revalidates their hashes: ControlSyntax `.olean` `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28`, `.ilean` `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1`; ControlTyping `.olean` `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e`, `.ilean` `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f`; CallContextTyping `.olean` `42c711d21b1f2d1cbd5486581448fce252d1b2bb9958329338ecf4dc9ac42204`, `.ilean` `1d32860c9c11b40785582a37f360987701b11d8f38dd3e85c8f5e0851e2d283a`; CallEntryTypingRepair `.olean` `0417fe931dda913d46712a601369424799963710c40cd1749afcc6b450e8de1e`, `.ilean` `967866bbd5badbe7b8deeb7d5bb4cd464ed95cbecf3d496702aab94fede1e7c5`; CallPeelingTyping `.olean` `de469ab6f25559f8c79b0f5242c310620b170e202dbdbebfba37f9343fa22df5`, `.ilean` `5d6b7afd92956b7ffe6ac715bf5e29aea0e49aea5a8fdb36601bc445179e5b4d`.

## Fresh resources and closure

Fresh total cap **1,440 seconds**, no carryover: one Sol/high author 600s; Luna verification 240s; fresh independent review 420s; integration 180s. Two serialized Lean invocations at most, each `-j1 -M1024`, 120-second timeout; one process, CPU 1, memory 1 GiB; Astra 0. Keep the three historical UNKNOWN reservations quarantined. No Rust/source/runtime/tests/paper edits are authorized.

Success: unchanged exact proposition compiles, signature is identical, axioms are within `[propext, Quot.sound]`, complete receipts are frozen, fresh review is CLEAN, and Luna integrates the result. Otherwise record `FAILED_VERIFICATION / UNACCEPTED` with the first exact obstruction. The r1 failure remains immutable; unrelated accepted results remain unchanged.
