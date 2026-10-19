# Sprint repeated-choice-20261020-r136 — Boolean-selected repeated continuation

Status: CANDIDATE pending prospective spec and compiler/source review; no writer lease until both pass
Branch / baseline: `research/simple-sub-intrusion` / `6c04fc08f76bc4cc2d71a3910e4aa476097a378b`
Contract revision: 1

## Original outcome and success evidence

Parent goal: implement Yulang inference/evaluation with proof-backed source correspondence while broadening unchanged Yulang2 sample behavior where the current compiler can support it. R136 is an independent evaluator-surface increment; it does not close Simple-sub, effect, soundness, principality, F5-replacement, or broader Yulang2 compatibility gates.

Outcome: expose one existing raw-continuation behavior as a runnable browser example. One source operation returns `bool`; the same captured continuation is resumed first with `true`, then with `false`; the first resumed result selects the second resumption; the final result is `23`.

Frozen source specimen (`web/playground/examples/repeated-choice.yu`):

```yu
act signal:
    our choose: () -> bool
my relay (thunk:[signal] int) = catch thunk { signal::choose(), k -> { my first = k true; case first: 11 -> k false, _ -> first } }
my main = relay { my choice = signal::choose(); if choice: 11 else: 23 }
```

Prediction only until authorized verification: running `main` returns `23\n`. Falsifiers include unsupported source admission, first result not controlling the `case`, altered Boolean response, failure to resume the same lexical `k`, expired-owner/receiver reuse, or any new runtime selection policy.

## Authority, source domain, and dependencies

Use current colon-form `if`, existing `case`, `catch`, Boolean literals, and the established operation syntax. No syntax, observable language rule, runtime policy, solver policy, or source-domain restriction is proposed. Do not touch R135's unapproved braced-if proposal. R98's failed distinct-receiver matrix and R99's forbidden fresh-receiver repair remain separate and must not be claimed as addressed.

Source evidence to reuse, with limits:

- `runtime_resume.rs::reusable_raw_context_writes_its_original_pending_local_cell` already exercises `k 11` followed by `k 23` in one handler.
- `runtime_resume.rs::raw_response_uses_the_declared_boolean_response_type` admits Boolean resumption into a colon-form conditional.
- `candidate_source.rs::preflight_catch_signature` admits primitive Boolean responses; `machine.rs::Frame::ResumeArgument` checks response values and resumes the captured template; `capture_template` records the retained suffix.
- These establish existing local examples and implementation owners, not a general theorem. The new source's ordered dependency and Web/CLI correspondence remain to be checked.

Pinned direct source hashes:

```text
tools/inference-playground/tests/runtime_resume.rs 449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580
tools/inference-playground/src/runtime/machine.rs 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/program.rs 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
crates/yu-solver/src/candidate_source.rs cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
web/playground/src/main.ts 39d0a5fd7031105649b40000237f63c37b5d3239b9b175ad0e3544a63e839301
web/playground/index.html e1a1caaf7d27a6765ba4bd5e5ec2447599a019ff1c4b56b8707a15fd00bb26cf
web/playground/smoke-test.mjs 099ffecad2ffd944ee84ba5a024f99c13c9a8aaa3a736390fedb23b2a6638c05
web/playground/package.json ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf
```

## Two continuing lanes after candidate approval

Proof lane: construct a finite source-to-execution trace for this exact source. Track the declaration, operation request, handler match, captured suffix/template, first resume with `true`, resulting `11`, `case` selection, second resume of the same `k` with `false`, and final `23`. Relate each step to the owning source constructors and consumers. Do not infer a general repeated-resumption or continuation theorem. Output `notes/theory/2026-10-20-r136-repeated-choice.md` and `tasks/agent-loop/inbox/20261020-r136-proof.md`.

Implementation lane (Luna/high only): one canonical source fixture at `web/playground/examples/repeated-choice.yu`; a CLI integration test includes that fixture; register it in `web/playground/src/main.ts` and `index.html`; add it to `smoke-test.mjs`. No runtime, solver, parser, HIR, or WASM source edits unless evidence shows a genuine contradiction; stop and return that authority/dependency change to Luna before any such edits. Output `tools/inference-playground/tests/cli_repeated_choice.rs` and `tasks/agent-loop/inbox/20261020-r136-implementation.md`.

## Exact leases and review boundary

Until this candidate receives CLEAN prospective review, only Luna may edit this contract, current state, and a review handoff. Candidate review leases: `tasks/agent-loop/inbox/20261020-r136-prespec-review.md` to a fresh `spec_auditor`; `tasks/agent-loop/inbox/20261020-r136-precompiler-review.md` to a separate fresh `compiler_referee`. Reviewers read this contract and listed dependencies, do not run code/tests/builds, and do not write implementation/proof outputs.

If approved, exact proof leases: the theory note and proof inbox above. Exact implementation leases: the canonical source, CLI test, three listed Web files, and implementation inbox above. Do not edit `runtime_resume.rs` or other existing expected-output tests. Only Luna integrates and performs Git.

## Verification, resources, gates, and stop conditions

Cap 1,800 active seconds: inventory/contract 120; prospective reviews 120; proof 480; implementation 360; final reviews 240; focused verification 360; closeout/integration 120. Zero Astra. One heavyweight process at a time. After review and implementation, run one isolated CLI test, then the Web playground check once. Stop at the first semantic failure; no retries or unrelated test runs without a revised contract. These focused checks are authorized by the continuing user goal to make sample code runnable.

Fresh final compiler/source and spec/regression review the frozen proof, implementation, direct dependencies, and intended test surfaces. A reviewer may not self-certify a result it authored. Any blocking/major finding keeps the sprint candidate unaccepted until a versioned correction is reviewed. Keep all original inference/evaluator A/B and production gates OPEN; a finite source trace and green checks close only this example's evidence slice.

Boundary: stop and return to Luna for any new language/runtime/solver policy, source-domain change, unpinned dependency, exhausted budget, failed exact CLI or Web check, altered expected output, unknown writer overlap, or any need to repair R98/R99. Only Luna grants writer leases, adjudicates reviews, updates `current.json`, stages explicit paths, commits, and non-forced pushes.
