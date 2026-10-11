# Oracle callback reuse across a local subtraction boundary

Date: 2026-10-11
Status: frozen, unreviewed executable characterization; global hygiene theorem remains OPEN
Yulang3 baseline: `b4a5dde3e00d9940b5c40701acc04094f0ea9495`
Oracle source revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle binary SHA-256: `0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58`

## Question and authority

The bounded question is whether a source can pass one callback through an
annotation-local call and then return that same callback for a later call, so
the callback's later effect must survive the earlier local subtraction. The
governing contract is [annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2, together with the original universal claim H in
[the Oracle hygiene proof](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. This probe does not weaken H or change the selected polarity policy.

## Exact bounded observation

The pinned Oracle checkout is `/tmp/yulang2-oracle-read`, at the source
revision above and with a clean worktree. The executable's SHA-256 matched the
previously recorded binary. I used the already-built executable; no build,
test suite, temporary source file, or output file was created.

The source was supplied on stdin to
`timeout 30s ./target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly`:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my through(cb: (() -> [tick] ())) = (\x -> x) cb
my route(cb: (() -> [tick] ())) =
    ((\() -> {
        cb ()
        \x -> x
    }) ()) cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
my observed_through() = (through provider) ()
my observed_route() = (route provider) ()
```

The command exited 0 in under one second with empty stderr and no diagnostic.
The decisive printed types were:

```text
direct: (() -> [tick; 'a] ()) -> () -> ['a#0[tick]] ()
through: (() -> [tick; 'a] ()) -> () -> ['a#0[tick]] ()
route: (() -> [tick] ()) -> () -> ()
provider: () -> [tick] ()
observed_direct: () -> ()
observed_through: () -> ()
observed_route: () -> ()
```

A separate direct-call control in one bounded invocation produced:

```yulang
pub act tick:
    pub ping: () -> ()
my provider() = tick::ping()
my direct_call() = provider ()
my higher_order(cb: (() -> [tick] ())) = cb ()
my use_provider() = higher_order provider
```

Its decisive types were `provider: () -> [tick] ()`,
`direct_call: () -> [tick] ()`, `higher_order: (() -> [tick] ()) -> ()`,
and `use_provider: () -> ()`.

The controls show that directly calling `provider` preserves `[tick]`, and
that returning it through ordinary identity preserves a generalized effect
tail. In contrast, the `route` source calls `cb` inside the annotated callback
boundary, returns that same `cb` through identity, and invokes it afterward;
the printed route and observed types contain no `tick` effect. This is a
source-qualified **candidate loss** at the displayed-type boundary and the
first useful discriminator for the source/replay audit.

## What remains unproved

This dump alone does not establish the raw annotation SubtractId, prove that
the returned callback's later effect contribution is independently attached
to the same source occurrence, expose the actual instantiated scheme map, or
show which normalization, replay, or compacted observation removed the effect.
It does not execute `observed_route`, demonstrate a runtime operation, or
prove that the displayed type is an accepted complete typing under the
selected source semantics. Therefore this is **not yet a source-qualified
counterexample to H**. The original universal H, Oracle adequacy, and Yulang3
implementation obligations remain OPEN.

The next decisive work is a source-owner bridge for this exact input: trace
the annotation occurrence into its raw identity and stored generalized
scheme, then follow the actual return and later-call output consumer. Preserve
the distinction between the first local subtraction and the later invocation
of the same callback. Do not infer identity from the display-only `#0` name.

## Execution record

An initial invocation omitted `--no-prelude --no-cache` and reached its
30-second timeout without output. The two bounded invocations with the exact
flags above completed normally (one for the full discriminator and one for
the direct-call control). No Oracle source files or Yulang3 files changed.
No independent review, runtime execution, build, Cargo command, or test run is
claimed.
