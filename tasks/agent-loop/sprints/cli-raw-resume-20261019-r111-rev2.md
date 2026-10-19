# R111: raw continuation resumption at the public CLI boundary

Status: DRAFT_FOR_PRE_EXECUTION_REVIEW. Revision 2 supersedes rev1 for new
work only; rev1 and its MAJOR pre-edit review remain preserved as failed
contract evidence. Primary and sole Git integrator: Luna
`/root`. Parent goal remains broad and balanced: six independent effect-hygiene
fronts, proof-backed method/role behavior, and early runnable ordinary/effectful
source execution. This packet advances one finite continuation
capture/resumption observation through the public stdin CLI.

## Two fixed existing source recipes

Use the exact two source recipes already present in
`runtime_receiving.rs`; do not simplify, strengthen, weaken or otherwise edit
either source. Neither source has a final LF.

Cell A, 255 bytes, SHA-256
`04d30eddc08b8ec472b2f969a947876cf235fb15a9576de574833fa673504cd5`:

```yu
act signal:
    our ping: bool -> bool
my receive (input:[signal] bool) = catch input { signal::ping(p), k -> { my first = k true; k false } }
my forward (pending:[signal] bool) = receive pending
my main = receive { my result = signal::ping true; result }
```

This source resumes the same raw continuation twice with distinct Boolean
responses. The original suffix result is returned by the second resumption.

Cell B, 224 bytes, SHA-256
`cdb662794420240f96490ff26a3ad29ee5f0726c3adca2936a7e7a730cd0a3e7`:

```yu
act signal:
    our ping: int -> int
my receive (input:[signal] bool) = catch input { signal::ping(p), k -> k 23 }
my forward (pending:[signal] bool) = receive pending
my main = forward { my ignored = signal::ping 7; false }
```

Here the operation response and continuation argument have type Int, while the
resumed saved suffix and final `main` result have type Bool. The original suffix
result is `false`.

For both cells, add one test named
`raw_continuation_resumes_publish_the_saved_suffix_result` to
`tools/inference-playground/tests/cli_raw_resume.rs`. Run two child processes
serially, passing each exact source to stdin with arguments
`--run main --steps 10000 -`. Each must exit successfully, print exactly
`false\n` to stdout, and leave stderr empty.

## Evidence boundary and falsifiers

The existing runtime integration test already prepares and runs these source
recipes through its public parse/lower/candidate/RuntimeProgram/Machine helper.
The reviewed primitive-root theorem and raw-template correspondence provide
finite reusable premises only within their explicit source/receiver/template
conditions. R111 adds a separate CLI stdin, preparation, result/status/stream
observation for the exact same bytes.

The proof must keep the raw continuation, original saved suffix, each response
value and final result distinct. In A, the two real `k` applications re-enter
the original continuation with `true` then `false`; the first result is stored
in an unused local and execution continues to the second call. In B, `k 23`
provides an Int response, the original suffix binds that operation result to
`ignored`, then computes its final Bool `false`. Do not identify operation
response type with the suffix result type.

No fresh-receiver authorization law from R99 is needed or authorized. The
source-level direct-receive and forwarded-receive forms are fixed by the two
existing recipes. If a proof of these exact sources requires the R99
fresh-receiver law, a new semantic rule, an unpinned source owner, or changing
either recipe, stop and return that precise obstruction; do not improvise.

Passing establishes only these two finite CLI paths. It does not prove
arbitrary Resume, arbitrary foreign continuations, general source/parser
completeness, continuation soundness, native residual adequacy, any full
Simple-sub/evaluator theorem, method/role lookup or dispatch, semantic adoption,
or production authority. R109's separate SourceSite range failure remains
untouched and supplies no premise here. No production edits or existing test,
fixture, expectation or diagnostic changes are authorized. Any command
failure, preparation error, wrong outcome/output, resource exhaustion or
identity mismatch stops without repair/retry.

## Exact command

After all proof/test output freezes and fresh post-output spec plus compiler/
source reviews are CLEAN, Luna alone may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_raw_resume raw_continuation_resumes_publish_the_saved_suffix_result -- --exact --nocapture
```

No alternate command, standalone build, formatter, direct CLI invocation,
retry or repair is authorized. Once the command begins, a compile/preparation/
test failure consumes the attempt. Preserve the result and stop.

## Frozen inputs

Hashes were checked against actual current bytes at contract preparation. Rev2
restores Cell A's unconditionally declared, though unused, `forward` binding
from the exact existing test recipe. Cell B is unchanged.

R111 rev1 contract SHA-256:
`71501d99556c25faac8d42afe82e195e583b4146f913e17b97740cada3459318`.
Its pre-edit review was MAJOR and is preserved at
`tasks/agent-loop/inbox/20261019-r111-pre-spec-review-rev1.md`. It blocks rev1
and grants no implementation authority.

| Input | SHA-256 |
|---|---|
| Current source recipes and existing runtime test `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| Reviewed primitive computation-root receiving theorem `notes/theory/2026-10-16-primitive-computation-root-receiving.md` | `a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606` |
| Reviewed raw-template correspondence `notes/theory/2026-10-16-runtime-resume-template-correspondence.md` | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| Runtime raw-resumption closeout `notes/progress/2026-10-16-playground-raw-resume.md` | `fea89067d065178b1fc61eb06ce98cada2c6bde21db46e8f0695b9abb085591c` |
| Runtime continuation constructors `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| Runtime machine `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Runtime program `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Receiver schema/evidence `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| Public CLI argument/stdin route `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Public prepare/execute/result mapping `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Atomic output/error caps `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| Existing stdin/child CLI convention `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Test target/package `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

No R109 fixture is a direct input. Any pin mismatch or required new owner stops
the packet until a versioned contract and fresh review.

## Leases, review and resources

- Proof lane owns only `notes/theory/2026-10-19-r111-cli-raw-resume.md` and
  `tasks/agent-loop/inbox/20261019-r111-proof.md`. It must bind exact source
  constructors, raw-template/resumption transitions, receiver lifetimes and
  final Boolean projection; distinguish source premises, reused evidence and
  R111 observations; preserve all exclusions above.
- Implementation lane owns only `tools/inference-playground/tests/cli_raw_resume.rs`
  and `tasks/agent-loop/inbox/20261019-r111-implementation.md`. It adds one
  serial two-subprocess test using these exact bytes and assertions.
- Fresh pre-edit spec review is assigned before implementation. Rev1 review
  output is `tasks/agent-loop/inbox/20261019-r111-pre-spec-review-rev1.md`;
  rev2 output is `tasks/agent-loop/inbox/20261019-r111-pre-spec-review-rev2.md`.
  Fresh post-output spec and compiler/source reviews are read-only; Luna records
  receipts at `20261019-r111-post-spec-review.md` and
  `20261019-r111-compiler-review.md`.
- Luna owns current state, exact command, closeout, next-action selection,
  explicit-path Git integration and push.

Workers inspect only the exact frozen inputs and leased outputs. Workers do not
run tests/build/compiler/runtime/formatter/CLI/Git commands. Only Luna's one
exact command is authorized after CLEAN reviews. Preserve the three inherited
UNKNOWN identities, board quarantine, historical R104 lease and legacy slot
reservation; allow at most two producers and do not reclaim any unknown lease.

Total ceiling: 1,500 seconds: proof 600, implementation 300, pre/post spec
reviews combined 120, compiler/source review 180, command 120,
integration/closeout 180; Astra 0. No renewal. Stop on a missing source owner,
source/pin mismatch, reliance on unauthorized R99 law, review blocker/major,
unexpected outcome or budget exhaustion.

## Breadth boundary

R111 is one bounded continuation-capture/resumption source-to-CLI slice. Other
hygiene fronts, R101-ENTRY-1, proof-backed method/role behavior, original
Simple-sub/evaluator quantifiers, R85 adoption and production authority remain
separate and open. After this slice, rotate to method/role source-corresponding
behavior as the user directed; do not continue deepening only one effect front.
