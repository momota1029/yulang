# Source-owned callback receiver attachment: provisional observation

Date: 2026-10-15
Status: attachment-only code implemented, independently reviewed and verified;
receiver lifetime, scope attribution, discharge and original sample remain OPEN.
Baseline: `9393af08e7de7471d6e46a9c308db100236ed346` (source code at b8a85e101).
Authority: the reversible inference-playground direction, directional protection
§2, and [conditional source-owner derivation](../theory/2026-10-15-playground-callback-hygiene-construction.md#6-original-formal-ownership-and-a-bounded-discharge-contract).

## Implemented owner

In scoped mode, the original formal registration retains its authentic Lambda
body occurrence and body region. An omitted-formal source Call joins its
resolved Parameter/registration to that original receiver, retaining separately
the demand's existing computation scope and lexical region. The experimental
Call observer validates the original Lambda/body and directional introduction.
The descriptor is constructed from source ownership, not reconstructed from
merged effect rows or a source spelling.

Only `candidate_source.rs` and `candidate_call.rs` changed. Context transforms,
capture/FreshUse, scope inventory ownership, grants, releases and Catch
consumption did not change. The descriptor has no semantic consumer. Ordinary
mode retains `None`; its fixed record-size overhead remains included by existing
`State::bytes()` capacity accounting. Construction adds constant metadata per
formal/Call and linear work in the existing traversal; no extra graph search,
cache or runtime receiver representation was added.

The new test target is `candidate_receiver_boundary_release`. Its name locates
the open seam; it does not assert that a receiver release was implemented.

## Discriminators and corrected observation targets

The final genuine source fixture uses curried `g h x` so the inner Lambda
captures the original h. It retains an independent direct operation, inner and
outer Catch, two distinct named callback providers and two g uses. The attachment
points to h's original receiver Lambda/body; its lexical scope remains different.
Direct operations acquire no omitted-formal attachment. Ordinary mode supplies
none of the experimental descriptors.

Internal tests additionally establish:

- The original `h 0` scope is the actual argument scope of `id (h 0)`.
  A nonidentity copied demand is authenticated by original Call, use instance,
  actual negative Function root, and shared scope/input provenance. Native
  ProtectBody and Release must refer to that **same copied scope and input**.
- At least two distinct authenticated nonidentity FreshUse images of the captured
  scope retain their lexical-region ownership. Original plus one copy would
  not suffice. Attaching the receiver does not change any of those owners.

Pre-write spec review found two major defects in the first provisional tests:
one expected raw-template activation, and one attempted execution of an
unsupported local-helper path. The authorized repair replaced the observation
target with an actual copied demand and the fixture with the curried control,
while retaining ownership/direct-operation assertions and strengthening two-use
evidence. Independent delta review closed both findings; assertions were not
changed to declare the unsupported path successful.

## Unresolved local-helper evidence

Subsequent checkpoint: the [scoped transport repair](2026-10-15-callback-helper-scoped-transport.md)
now admits the unchanged grouped source below and checks its actual copied h
projections. The original failure and diagnostic uncertainty recorded here
describe the attachment-only checkpoint; receiver discharge and full hygiene
remain OPEN.

The original provisional integration fixture had an ungrouped block after
`catch`; the parser treated that brace as the arm list, leaving no scrutinee.
Grouping it fixed syntax. This fixture failure did not establish a general
lambda-syntax limitation. Its grouped local-helper source then failed scoped
inference with `Solve(ReceiptMismatch)`; ordinary inference succeeded:

```yu
act signal:
    our ping: () -> int

my invoke cb = cb 0
my g h = catch ({ my step i = h i; my direct = signal::ping(); invoke step }) {
    signal::ping(), _ -> 1,
    v -> v
}
my callback_first i = signal::ping()
my callback_second i = signal::ping()
my first = catch g callback_first { signal::ping(), _ -> 2, v -> v }
my second = catch g callback_second { signal::ping(), _ -> 3, v -> v }
```

The exact failing receipt owner was not isolated. Missing copied demand root,
copied-root authentication and replay are diagnostic candidates, not findings.
This is retained evidence of the scoped source-coverage gap, especially relevant
to the original loop's captured h. It is not a language rejection or a resolved
test expectation. The smaller curried success does not close this case.

## Review and verification

M2 used one implementer, one compiler referee for source/authentication and
accounting, and one spec auditor for the test-contract repairs. Both reviews
converged without remaining findings. The mathematical/source delta has its
separate conditional review and keeps the original parent gate OPEN.

Commands used `CARGO_BUILD_JOBS=2`, `timeout 300s` and one test thread:

| Command after `cargo` | Final result |
| --- | --- |
| `test -q -p yu-solver --features shadow-apply-candidate --test candidate_receiver_boundary_release -- --test-threads=1` | 2 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --lib receiver_attachment -- --test-threads=1` | 2 passed, 694 filtered out |
| `check -q --workspace` | passed, no warnings |
| `build -q -p yu-playground` | passed, no warnings |

There were six receiver test commands including four diagnostic failed runs
before the final two passing runs. These are not additional passed cases.
Three final CLI processes with `--scoped-experiment --intrusion` on retained
`compose-scoped-identity.yu`, `compose-scoped-two-uses.yu` and
`compose-scoped-independent.yu` exited 0 with empty stderr, each under 15 s and
the existing 1 MiB output bound. They are admission/regression observations,
not a new proof of every protection fiber. No benchmark or timing repetitions.
Two additional tiny CLI fixture diagnostics established the syntax repair;
the worker also read CLI help once. Logs are under
`/tmp/yulang-callback-exact-20261015/`.

`rustfmt --edition 2024 --check` on the new test and `git diff --check` passed.
Broader test suites, native runtime, local-helper repair and general
soundness/principality verification were omitted; their gates remain open.

## Next semantic seam

Subsequent authority update: the [direct user decision](../design/2026-10-15-callback-identity-forwarding.md)
requires the same outer return through ordinary `id`. The historical open
behavioral alternative below is resolved; source attribution and construction
remain OPEN. This changes neither the recorded attachment-only implementation
nor its proof scope.

The [actual identity observation](2026-10-15-callback-identity-scope-observations.md)
does not decide whether the original h witness is the released argument e
witness or an independently licensed witness. The reviewed derivation permits
both conditional branches and requires actual source attribution. A pending
question at `questions/2026-10-15-callback-identity-release/question.md` asks
that exact behavior. No guard/expiry/subtraction repair was adopted while it
remains unresolved. The exact original Oracle execution is recorded
[separately](2026-10-15-exact-callback-hygiene-oracle.md).
