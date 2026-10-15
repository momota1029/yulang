# Playground primitive computation-root receiving

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Baseline: `1b85c4498`; runtime proof inputs unchanged from `ddda9bc67`
Status: local source theorem, matcher and focused execution gate complete;
general inference, full source correspondence and production/F5 remain OPEN
Mode: M1; one independent semantic reviewer, pre-write proof and actual delta
Authority: existing computation-entry/annotation-permission policy and typed
matching-path transport; no new language or negative-visibility decision

## Change and proof correspondence

`RootCompSchema::from_parameter` now authenticates the four existing rigid
ground results Unit, Int, Bool and Str for an explicitly annotated outer
Computation formal. The original Lambda/annotation/formal identity guards and
explicit-effects requirement are unchanged. Variable and Function results
remain outside this local certificate.

The [constructive source theorem](../theory/2026-10-16-primitive-computation-root-receiving.md)
derives the fresh local positive certificate, exact same-view receipt/Observe
join, whole-formal Name forwarding and ground-result projection uniformly.
Each ground value has no latent effect position corresponding to the consumed
computation root. The audit checks every entry, Grant, return and raw-template
View constructor/consumer. The existing compatible source typing, OpCompat,
original packets/owners and currently admitted continuation premises remain;
HIR construction or test success supplies no MODEL theorem.

`checked_result_semantics` independently returned CLEAN before implementation
at proof producer SHA-256
`5762f347035b021e7812501b5e4d57c07f7e0941b0c4d51f44c9c7b5eb1b35d0`,
then CLEAN for the actual matcher/tests and README. Primary accepts this exact
local scope. The README changes only two coverage sentences; its existing Int
example and other limits remain.

New tests exercise each additional root directly and through whole-formal
forwarding with repeated Resume and original pending local cells. An Int
operation response followed by a Bool suffix distinguishes response checking
from final computation-root projection. Empty/wrong-family permissions and
a nested helper owner fail to supply Grant for each new root. Private schema
checks retain all identity/effects/unsupported-shape guards. Every old
expectation, assertion and test name is preserved.

Reviewed/current receiving SHA-256:
`8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`.
Final integration-test SHA-256:
`f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf`.
The reviewed `ab56360e...caabc` test differs only in rustfmt layout of its new
Unit table row; primary inspected that mechanical correction. README SHA-256:
`59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6`.
No other runtime or compiler file changed.

## Exact verification and budgets

Primary serialized Cargo with `CARGO_BUILD_JOBS=2`, a 180-second command timeout
and one test thread:

```text
cargo test --locked -p yu-playground --test runtime_receiving --test runtime_resume -- --test-threads=1
cargo test --locked -p yu-playground --lib runtime::receiving::tests:: -- --test-threads=1
rustfmt --edition 2024 --check tools/inference-playground/src/runtime/receiving.rs tools/inference-playground/tests/runtime_receiving.rs
git diff --check
```

Results: receiving **18 passed**, raw-Resume **13 passed**, private receiving
**3 passed**; zero failed/ignored/warnings. The integration run completed before
the formatting-only Unit row correction; no behavioral change followed it.
Logs/resources: `/tmp/yulang-primitive-root-{receiving,schema}-20261016.*`.
Observed build/check process resources: integration 3.15s / 175,604 KiB peak RSS;
private module 1.69s / 206,372 KiB. These are bounded verification observations,
not performance benchmarks.

Three additional CLI processes ran:

```text
cargo run --locked --quiet -p yu-playground -- --run main -
```

Their stdin files `/tmp/yulang-primitive-root-cli-{bool,str,unit}-20261016.yu`
declare matching primitive operations, receive them through the corresponding
explicit ground computation formal and resume their saved continuation.
All exit zero with no stderr; outputs are respectively `false`, `"resumed"`,
`()`. Matching `.log` files retain the results. Each process had a 60-second
timeout and completed in under one second.

No full playground package, solver or workspace suite was repeated: the scoped
receiving/Resume consumers and schema module cover this M1 matcher delta;
the unchanged whole package last passed all 108 cases at the preceding native
checkpoint. That historical count is not the current package inventory.
Static artifact links, frozen dependency pins and scope checks accompany
integration. Performance budget consumed: **0 experiments/processes/samples**.
The production cost is a fixed four-way tag predicate; no retained storage,
allocation, loop or representation change is added.

## Remaining scope and records

Unknown inherited coverage stays unknown. A concrete family needs its exact
original permission and same-view receipt under the live original receiver;
schema presence creates no negative certificate. Function/unknown roots,
nonprimitive operation interfaces, arbitrary adapters/full profile coverage,
full source typing/MODEL, full-domain Resume, generalization/native inference
and production/F5 retain their separate OPEN gates.

`tasks/current.md`, `tasks/research-lab.md`, the source-theorem status and design
index are synchronized. Pending question drafts remain excluded from staging.
