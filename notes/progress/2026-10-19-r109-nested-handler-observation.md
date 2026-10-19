# R109 closeout: nested-handler execution observation

Status: **FAILED_TO_ACHIEVE_FIXED_SOURCE_SITE_RANGE_ASSERTION**. The one
authorized command ran once. No retry or repair is authorized or performed.

## Command receipt

Exact command:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_handler_priority nested_handler_priority_and_shallow_arm_requests -- --exact --nocapture
```

Exit code: `101`. Cargo compiled the test profile successfully in `2.48s`,
started one test, and the test failed in `0.07s`. Existing dead-code/unused
warnings were emitted from `yu-hir`, `yu-solver`, and `yu-playground`; the build
completed despite them. The process result was:

```text
running 1 test

thread 'nested_handler_priority_and_shallow_arm_requests' (1960612) panicked at tools/inference-playground/tests/runtime_handler_priority.rs:105:5:
assertion `left == right` failed
  left: 128..130
 right: 121..130
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
test nested_handler_priority_and_shallow_arm_requests ... FAILED

failures:

failures:
    nested_handler_priority_and_shallow_arm_requests

test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.07s

error: test failed, to rerun pass `-p yu-playground --test runtime_handler_priority`
```

This is the complete test-result output returned after compilation. No retry,
alternate command, build-only command, repair or fixture edit followed.

## What the test reached

The test runs its three cells sequentially inside one test case. The first exact
cell returned completed integer `11`; the second, with only the inner arm order
swapped, returned integer `23`. In cell C, parse/lower/candidate/runtime/start
preparation succeeded; the machine returned an outward `tick` request with the
expected HIR operation identity and integer payload `11`. The initial-request
range inequality also passed. The final source-range equality failed:

- Actual `SourceSite.range`: `128..130`.
- Expected range: `121..130`.
- The existing test expects the selected source slice to be `::tick 11`.
- The actual range selects only the last two bytes, `11`, according to the
  assertion's own reported offsets.

Therefore R109's finite observation did **not** achieve its complete fixed
outcome. The exact source-to-outward-request preparation path was runnable, and
the first two handler-order results plus C's operation/payload assertions held;
the specified Apply-tail provenance assertion did not. No claim is made about
the assertions after the panic, full source-root/occurrence identity, dynamic
event identity, stack frames, native residual correspondence, or any universal
property.

The test, fixture, expectations, production code and proof were not edited.
This mismatch is an observation, not a diagnosis of whether the producer,
contract's expected range, or another source-site assumption is at fault. That
question requires a separately versioned and reviewed sprint; it cannot be
repaired inside R109.

## Review and scope boundaries

Before the command, the R109 contract, proof and implementation inventory had
fresh CLEAN pre-spec, post-output spec and compiler/source reviews. The reviews
confirmed the exact pins, current conditional frame/receiving path, and explicit
finite-probe authority. The program.rs historical pin was not used as current;
the appended test-only suffix was independently checked without Git.

R101 and R102 remain `FAILED_TO_ACHIEVE_CONTRACT_PREREQUISITE`; their commands
remain `NOT_RUN`. `R101-ENTRY-1` remains `OPEN`; this finite attempt does not
establish static parser/CST completeness. The six broad hygiene fronts,
method/role obligations, original Simple-sub/evaluator claims, R85 adoption and
production authority remain open. No semantic rule or production behavior
changed.

Frozen inputs and outputs:

- Contract: `tasks/agent-loop/sprints/nested-handler-observation-20261019-r109-rev1.md`, SHA-256 `834bf38f690b9fa9fc617a57e40e1c09bbce996949176aafdf5f6e995bc8eb43`
- Conditional proof: `notes/theory/2026-10-19-r109-nested-handler-observation.md`, SHA-256 `bf540b6e44f4c490f08c7afd83b276b0105b4d6d70ef156f4786625d28e0b8c6`
- Proof handoff: `tasks/agent-loop/inbox/20261019-r109-proof.md`, SHA-256 `bb1c3da475fdcda98b83e3fd7bc3c0c1328be796502b1edf14d337974b27059b`
- Read-only inventory: `tasks/agent-loop/inbox/20261019-r109-implementation.md`, SHA-256 `32094364786d9700bd449dfb4a8992c68d33cc23d5bf0a27c0710ccd5d0ae24e`
- Pre-spec review: `tasks/agent-loop/inbox/20261019-r109-pre-spec-review.md`, SHA-256 `f0900e07e7d3539eb18a59bbc65e5e5d4e576c1ec6863e461149b829366d6a95`
- Post-spec review: `tasks/agent-loop/inbox/20261019-r109-post-spec-review.md`, SHA-256 `73e9233b88bf4c71b7eeb2725da02bb922db697d4d4d60bff6eb95526336275a`
- Compiler/source review: `tasks/agent-loop/inbox/20261019-r109-compiler-review.md`, SHA-256 `c3f1cee417ad5cc106ace16b432f4a10e849a00ffe85a6a31c4aada2c5a27e65`
- Existing test, unchanged: `tools/inference-playground/tests/runtime_handler_priority.rs`, SHA-256 `cdcb06ceebcca48cd3ff6fbc1a429243e9013a148c5fc895d9926e5dc2ce07db`

Next selection should rotate to an independent open hygiene front or the
method/role and executable-source track. It must not repeat this fixture or
silently correct its range expectation.
