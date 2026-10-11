# Oracle callback reuse: adversarial policy audit

Date: 2026-10-11
Status: frozen, unreviewed research checkpoint; H remains OPEN
Method: adversarial source-contract inspection and reduction of recorded evidence
Yulang3 assignment baseline: `b4c294ae69586805f92e966cbde8fae3ebe2b621`
Oracle source revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note only; no delegation, Git operations, executions, builds or tests

## Objective and governing premises

Try to defeat the candidate conclusion that returning an annotated callback and
calling it later loses an independently surviving provider effect. Authority is
[the selected annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The original universal H remains exactly the statement in
[Oracle global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1: every successfully lowered program, composed-negative occurrence, original
scope/binders, actual instance and actual call/output route; attached subtraction
must preserve independent same-family contributions, symbolic connections,
checks and correlated lineage. This audit neither narrows that domain nor
proves its instance/generalization premises.

The callback result withdrawn in the governing policy's §6 supplies no expected
scheme. This note derives a conditional expectation from the selected local
policy and Oracle contracts instead.

## Contract audit

In `cb: (() -> [tick] ())`, the parameter position reverses polarity and the
callback result-effect position preserves it. Therefore `[tick]` is composed
negative relative to the receiving function. The selected policy permits
subtraction **inside that receiving function**. An invocation of the returned
callback in a different root function does not acquire a new negative concrete
annotation merely because its callee previously crossed that parameter.

The frozen Oracle's `web/docs/reference/effects.md`, “Effect annotations and
visibility” (around lines 244–266), explicitly describes an argument annotation
as a contract allowing handlers **inside the receiving function** to consume
the named effect. “Propagation” (around lines 273–278) says a caller acquires
an effectful callee's effect unless a handler can see and consume it. “Handler
hygiene” (153–199) prohibits taking caller-supplied effects merely by family
identity. These contracts supply no rule making a returned provider permanently
pure. The source contains no `catch` or other source handler.

The selected subtraction policy still permits removal from the first `cb ()`
inside `route`; the absence of a handler does not by itself invalidate that
selected static subtraction. The important boundary is the later invocation,
after returning from `route`, not the first local invocation.

The actual call constructor `crates/infer/src/lowering/expr/tail.rs`,
`make_app_with_origins` (535–624), constructs a function demand with a fresh call
effect and connects the callee evaluation effect and returned call effect into
the application effect. It also consults a local callee projection and extends
the current latent predicate. The output owner in `lambda.rs` (1232–1237) wraps
both result Value and Effect with predicate subtraction. Thus there is an actual
representation route by which evidence affects returned values; existence of
that route does not prove that exporting its effect into a later root is
permitted by the local policy. The exact predicate supplied on this input and
its later consumer remain the constructive prover's obligation.

## The smaller discriminator is already in the recorded run

The [frozen probe](2026-10-11-oracle-callback-reuse-projection-probe.md) records:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

In the recorded larger source, these definitions print:

```text
direct: (() -> [tick; 'a] ()) -> () -> ['a#0[tick]] ()
provider: () -> [tick] ()
observed_direct: () -> ()
```

This is a reduced witness **extracted from an existing run**, not a separately
executed minimal program or a claim that removal of the other definitions was
tested. It is smaller and more discriminating than `route`: it has no first
local invocation to subtract, no anonymous function, and no preliminary
unhandled `tick` operation that could prevent reaching the later invocation.
The latter is a real limitation of inferring dynamic behavior from `route`:
its first operation need not return in an unhandled execution.

The separately recorded direct-call control prints
`direct_call: () -> [tick] ()` for `provider ()`. The recorded identity wrapper
`through` also retains a latent annotated tail while `observed_through` prints
pure. Consequently, tail preservation in the direct/identity schemes does
**not** establish survival in their later caller. The observations localize the
question to use/observation of the returned callable, rather than uniquely to
the extra call inside `route`.

## Claim class, expected effect and remaining blocker

**Observed dump fact:** the recorded Oracle accepts the source in dump mode and
prints `provider` effectful, `direct` with a latent evidence-bearing tail, and
`observed_direct` pure. This is inherited executable evidence, not a new run.
Display `#0` supplies no raw SubtractId identity.

**Conditional source-semantic inference:** if returning `cb` preserves the
callable provider's operation behavior, and the published caller row is a
complete effect observation, then `observed_direct` must retain concrete
`tick`. Its only operation-producing invocation is outside `direct`'s local
scope and has no source handler. For `observed_route`, subject additionally to
reaching the second call, the first call's permitted local subtraction cannot
justify removing that later invocation's contribution. No exact full scheme
for `direct` or `route` is claimed.

**Actual counterexample to H:** not established. The remaining premises are the
exact source-to-provider behavior and actual instance/attachment/output map,
plus adequacy of the printed pure row as complete publication. Neither the
visibility prose nor a fresh-variable call constructor proves these premises.
No inspected source rule conclusively makes the pure later-call result
acceptable under the selected local policy. Conversely, the dump alone cannot
establish the actual independent contribution required to refute H.

There is no independent executable oracle in this lane. The policy and Oracle
documentation constrain interpretation independently of the recorded printer
output, but Oracle documentation and implementation share project assumptions.
No transition checker, numerical search, seeds, input ranges or mutation runs
were used. Existing `direct`/`through`/`route` variants discriminate source
structure only within their recorded runs. Missing instance maps, actual
runtime markers, replay/compaction behavior or display adequacy would defeat
promotion of this inference to a source-qualified counterexample.

## Commands, budget and handoff

Four lightweight source-read commands were used: required rules/skill and
frozen dependencies; authority/concurrency and source locator reads; frozen
probe/H plus Oracle public invariants; Oracle effect contract and bounded
call/output/annotation owner reads. Commands used `cat`, `sed` and `rg` only.
Some oversized aggregate output was truncated and one attempted `call.rs` read
found no file; the actual call owner was then read in `tail.rs`. No claim relies
on omitted output. Zero Oracle executions, tests, builds, measurement samples,
Git operations or child agents. Commands each returned in approximately 0.1 s;
total task wall time, peak RAM and actual runtime model/effort were not measured
or supplied. Only the leased note was written using `apply_patch`.

No dependency was edited. Supplied revisions were used; current hashes and
equality to the primary's baseline were not independently rechecked within the
four-command budget. Artifact whitespace/link checking is deferred to the
primary. Dynamic behavior, full replay/generalization, raw IDs and all source
cases outside these recorded examples remain unverified.

Recommended next action: have the assigned constructive lane trace the reduced
`direct`/`observed_direct` pair's stored return scheme, actual later-call effect
and final observation; it isolates the necessary bridge without the first
unhandled call in `route`. Keep H OPEN until that bridge and fresh independent
review establish a proof or counterexample.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-oracle-callback-reuse-policy-falsification.md`.
- Baseline SHA: `b4c294ae69586805f92e966cbde8fae3ebe2b621`; Oracle revision `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none caused by this worker; final dependency hashes/revision equality not rechecked.
- Review status: frozen, unreviewed research characterization and conditional inference; no independent review or H closure claimed. Writes stop at handoff.
- Checks already run: four bounded static reads; recorded probe/control outputs inspected. No new executions or artifact checks.
- Proposed commit message: `research: isolate returned callback policy discriminator`.
- Shared-record deltas left for primary/curator: record `observed_direct` as the smaller existing discriminator; distinguish latent-tail preservation from later-caller survival; retain H and publication/instance correspondence OPEN. No task, index, authority, question or shared theory map was edited.
