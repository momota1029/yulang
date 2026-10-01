# Typed family arguments across independent instantiations

Date: 2026-10-01
Status: frozen-Oracle characterization; not a symbolic-preservation proof
Oracle revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`

## Probe

```yu
pub act ask 'a:
  pub get: () -> 'a

pub answer_int(action: [ask int] _) = catch action:
  ask::get(), k -> answer_int(k 10)
  v -> v

pub answer_bool(action: [ask bool] _) = catch action:
  ask::get(), k -> answer_bool(k true)
  v -> v

my generic() = ask::get()

(
  answer_int(generic()),
  answer_bool(generic())
)
```

The same generalized `generic` definition is used once under each of two
independent handlers. Its inferred result type and effect family argument must
agree at each use.

## Observations

The frozen checker exits successfully. In `--poly-raw`, `generic` has one
quantified type variable shared by its result and `ask` family argument: its
result is `α` and its return-effect row is `[ask α]`. In `--mono`, the first
use has `unit -> thunk[[ask(int)], int]`; the second has
`unit -> thunk[[ask(bool)], bool]`. The interpreter and evidence VM both exit
successfully with roots `(10, true)`.

Commands, all run against the prebuilt CLI with `--no-prelude --no-cache` and
the scratch-only `YULANG_INTRUSION_{OWNER,ROLE_DEP,GUARD}_TRACE` variables
explicitly unset:

```text
env -u YULANG_INTRUSION_OWNER_TRACE -u YULANG_INTRUSION_ROLE_DEP_TRACE -u YULANG_INTRUSION_GUARD_TRACE \
  yulang --no-prelude --no-cache check /tmp/yulang-typed-family-lifecycle.yu
env -u YULANG_INTRUSION_OWNER_TRACE -u YULANG_INTRUSION_ROLE_DEP_TRACE -u YULANG_INTRUSION_GUARD_TRACE \
  yulang --no-prelude --no-cache dump /tmp/yulang-typed-family-lifecycle.yu --poly-raw
env -u YULANG_INTRUSION_OWNER_TRACE -u YULANG_INTRUSION_ROLE_DEP_TRACE -u YULANG_INTRUSION_GUARD_TRACE \
  yulang --no-prelude --no-cache dump /tmp/yulang-typed-family-lifecycle.yu --mono
env -u YULANG_INTRUSION_OWNER_TRACE -u YULANG_INTRUSION_ROLE_DEP_TRACE -u YULANG_INTRUSION_GUARD_TRACE \
  yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-typed-family-lifecycle.yu
env -u YULANG_INTRUSION_OWNER_TRACE -u YULANG_INTRUSION_ROLE_DEP_TRACE -u YULANG_INTRUSION_GUARD_TRACE \
  yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-typed-family-lifecycle.yu
```

The binary is `/tmp/yulang-intrusion-scc-owned-trace/target/debug/yulang`,
used against a checkout whose `HEAD` is the clean frozen revision above. That
worktree currently has uncommitted trace-only edits to inference/runtime files
and temporary tests. The inspected compiler/runtime source diffs are
environment-gated diagnostics or test additions, and all probe runs left
those environment flags unset; no semantic delta was identified in the
affected execution paths. The binary was not rebuilt as part of this probe,
so its exact artifact-to-source hash was not independently verified. No
frozen source file was modified by this probe.

## What this establishes

This is final behavior evidence that one polymorphic typed-family occurrence
can be instantiated independently at `int` and `bool`, with its result type,
effect row, and handler continuation agreeing at both uses. It is useful
Oracle-capability evidence for the successor's fresh-instantiation behavior.

The printed monomorphic rows are materialized observations. They do not prove
that the Oracle retains a symbolic invariant constraint through solver
residualization, generalization, or its own instantiator; they do not exercise
SCC intrusion; and they do not test two same-path family instances meeting
inside one row operation. In particular, this probe does not weaken the user
requirement that the successor carry symbolic `InvArgs` constraints through
solving, residualization, generalization, fresh instantiation, and intrusion.
It also does not address the separate accepted `ask<bool>` / `[ask int]`
soundness conflict.
