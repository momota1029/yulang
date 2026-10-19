# Sprint R118 — nested outside selection and a separate test-fixture repair

Status: CANDIDATE until fresh pre-spec review and Luna's grant.  
Branch / baseline: `research/simple-sub-intrusion` at `6caae031058b53545e03a205be2ab1bab9179a44`.  
Contract revision: 1; Luna owns contract, exact leases, verification, integration and Git.

## Original outcome and success evidence

Parent goal: proof-backed inference/evaluator progress with broad, deep work.
Continue rotating bounded evidence across all six effect-hygiene fronts, method/
role proofs, and runnable ordinary/effectful source. This sprint advances the
ordered-handler/outside-selection front and removes a separate test-compilation
obstruction. It makes no language-semantic, expected-output, production or
adoption change. R117's `cargo check` PASS and `cargo test --lib` failure at two
missing `capture_forest` fields remain frozen historical receipts; this sprint
uses new commands and does not retry R117.

**Proof/source outcome.** For the exact source below, construct a finite
source-to-runtime trace: the `io::other 7` request selects the inner handler;
its single arm emits `io::tick 11` in the outside context; the still-active outer
handler selects its single arm and returns `11`. Connect source operation
identity, the same-HIR `execute` path, installed `CatchReturn` frames, the
selected arm and final public result. This is a conditional finite witness, not
a general priority, permission, soundness, evaluator or static-to-native
theorem. Both handlers have one operation arm, so no duplicate-arm tie-break
premise is used.

Exact source (235 bytes, no final LF), SHA-256
`b8ad07fdbb59c06fdd46b9417f92acfe05c954faed34a2d0ca88ba500e58e900`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::other(p), _ -> io::tick 11 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::other 7))
```

The prediction is that public `--run main --steps 10000 -` exits successfully,
prints exactly `11\n`, and writes empty stderr. Falsifiers: the first request is
not selected by the inner arm; the inner arm's new request does not run outside
the consumed inner installation; the outer arm fails to select it; the CLI
returns a different result/stream; or any claimed source/runtime identity join
is not established by the pinned owners. Preserve R109's failed range fixture
and assertion unchanged; this is a distinct source witness.

**Implementation outcome.** In `crates/yu-solver/src/shadow_apply.rs`, complete
the two existing test-only `Graph` initializers at lines 2322 and 2427 with the
authentic `ForestSnapshot` from each fixture's owning `GraphState`. For the
empty test state, call its snapshot constructor; for the merged candidate state,
snapshot that exact candidate's intrusion forest. Do not fabricate an empty or
default snapshot for the nonempty fixture. Add one test-only public stdin CLI
observation of the exact source above. Do not edit runtime semantics, existing
tests or expectations. The first new command must prove solver unit-test target
compilation; the second observes only this new finite CLI cell.

## Authority, dependencies and immutable inputs

Governing approved semantic direction: `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`
§§14–15, SHA-256
`547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`.
Those sections select outside shallow matching/arm execution and explicit
shallow reapplication for derived deep behavior; they do not establish source
soundness, a general runtime installation-order theorem or implementation
authority. The ordinary source computation package is Draft and context
only. Its hash is `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917`.
R117 remains conditional; `R117-JOIN-1`, R100-P2, R85 adoption, all six effect
parents, original evaluator and Simple-sub A/B remain OPEN.

Relevant exact source pins at the baseline:

```text
crates/yu-solver/src/shadow_apply.rs 5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb
crates/yu-solver/src/candidate_scheme.rs 2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
crates/yu-solver/src/candidate_intrusion.rs 8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/tests/runtime_handler_priority.rs cdcb06ceebcca48cd3ff6fbc1a429243e9013a148c5fc895d9926e5dc2ce07db
tools/inference-playground/tests/runtime_primitive.rs 2b6a99690e43442c9553786c420c7108bcc8d8d9974391b4f677b73572bac3db
notes/progress/2026-10-19-r109-nested-handler-observation.md 86fb0949fd87f66dbebc6c9615e4987607f6590f49655b2b649a8f8cac34da89
notes/progress/2026-10-19-r116-closeout.md 83428c5cc28254d6d7e7acde7c123d64586864331674fdb3fe20ae3a30912622
```

`Graph::capture_forest` is test-only evidence consumed by capture/replay
assertions. The authentic constructor is
`GraphState.intrusion.forest_snapshot()`; production graph capture already uses
that exact operation. The CLI `execute` entrypoint prepares one HIR, solves
from it, then constructs `RuntimeProgram` from the same HIR. Runtime request
propagation inspects the installed top `CatchReturn`, checks its arms in stored
order, removes a selected shallow handler before evaluating its arm, then
propagates any arm request against the remaining outer stack. Verify these
facts against the pinned bytes; they are not substitutes for the conditional
proof or observable CLI cell.

The source witness has two different operations in one declared family and
exactly one matching arm in each installed handler. Do not reuse R109's source,
change its range, or update its expected output. Do not edit any file beyond the
exact leases below. If the forest owner or public caller requires another path,
stop and return to Luna before writing.

## Two continuing lanes

**Proof — Sol/high, 480 seconds.** Construct the finite source/HIR/runtime
trace, relate both operation IDs and handler-arm owners, follow request
propagation through the consumed inner and retained outer frame, and apply the
result to the ordered-selection parent without strengthening it. Write only:

- `notes/theory/2026-10-19-r118-nested-outside-selection.md`
- `tasks/agent-loop/inbox/20261019-r118-proof.md`

No source edits, builds, tests, CLI or probes. Freeze one handoff with the
original parent, conditional premises, falsifiers, source/native bridge and
remaining owner.

**Implementation — Luna, 420 seconds.** Repair the two fixture initializers
using the authentic state snapshots, add the exact CLI test, and write only:

- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/tests/cli_nested_handler_selection.rs`
- `tasks/agent-loop/inbox/20261019-r118-implementation.md`

No changes to compiler/runtime behavior, existing fixture expectations,
`questions/`, or any other path. No command before all outputs freeze and fresh
review is CLEAN. Keep the fixture repair and handler observation as separate
commit-ready slices; Luna alone stages and integrates them.

Fresh review after both writers stop: a compiler/source reviewer checks the
conditional proof and exact owner trace; a spec reviewer checks §14–15 authority
and theorem boundaries; a regression reviewer checks authentic forest snapshots,
unchanged old fixtures and the new CLI observation scope. Authors do not review
their own work. No review may promote an open parent or unadopted design.

## Verification and resources

Total cap: 1,800 active seconds — source/contract inventory 120; proof 480;
implementation 420; independent reviews 360; verification 240; closeout 180.
Astra 0. At most two producers; preserve the three inherited UNKNOWN
reservations. Reviews begin after both write lanes stop. One heavyweight Cargo
process at a time, `CARGO_BUILD_JOBS=2`. The new commands are not retries of
R117:

```sh
cargo test -p yu-solver --lib --no-run
cargo test -p yu-playground --test cli_nested_handler_selection -- --nocapture
```

Luna runs both in one monotonic 240-second coordinator; admit each command only
when at least 120 seconds remain, stop at the first failure, kill the command
process group on timeout, and do not retry. The second command is admitted only
after command one passes and the exact new CLI test compiles. Failure or
non-admission leaves the corresponding result OPEN and does not alter R117's
record.

Success means: both independent reviews are CLEAN; authentic forest provenance
is retained in both test fixtures; the new CLI cell passes with exact `11\n`
and empty stderr; the proof artifact states exactly the finite conditional
trace and residual premise; all six effect parents and method/role parents
remain honestly OPEN. After closeout, rotate toward R100-P2's missing member
producer or R85's adoption gate, keeping runnable ordinary/effectful evidence
and the other hygiene fronts in the plan.

Stop at a missing ordering premise, invalid authentic forest snapshot, changed
source pin, blocking review, command failure, budget boundary or live lease
ambiguity. Consult the selector at a material obstruction, dependency/lease
change or sprint end, not per lemma or test.
