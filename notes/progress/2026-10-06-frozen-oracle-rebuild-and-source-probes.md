# Frozen Yulang2 Oracle rebuild and source probes

Date: 2026-10-06
Status: Primary-run compatibility characterization; no successor parity claim
Current branch/baseline: `research/simple-sub-intrusion` at `3bba19d72e33c7d1f2ca533e4c9268f7c0400590`
Oracle source: frozen Yulang2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Implementation authority: none

## Purpose and result

The previously inventoried executable artifacts were not provenance-verified
as the frozen `a58eefc31` Oracle. This note records a fresh build from that
exact source commit and tiny CLI probes of three source shapes now used by the
shadow/source-formation work. The build establishes an available frozen source
runner in `/tmp`; the probes show Oracle-side acceptance and printed schemes.
They do not compare the result with current successor schemes, prove the
source-registration rule, or authorize production inference changes.

## Reproduction

A detached worktree was created at the frozen commit:

```text
git worktree add --detach /tmp/yulang2-oracle-rebuild a58eefc31e22141574b6f20c6a5748151c6d79f1
```

The worktree `HEAD` was verified as the full commit above and had no source
changes after the build. The package build used the frozen lockfile and a
dedicated target directory outside both source worktrees:

```text
CARGO_TARGET_DIR=/tmp/yulang2-oracle-target RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo build --locked -p yulang --bin yulang
```

It completed in the dev profile in 1 minute 26 seconds, with at most two
Cargo jobs. The frozen `infer` library emitted 105 compiler warnings; no
source file was changed to address them. No tests or broad suite were run.
The resulting ELF executable is
`/tmp/yulang2-oracle-target/debug/yulang`, SHA-256
`5adb95e4bd22099c96cb61d0fbf484ea9da1cc1f9be5db2a849e2eebba44a8dc`.

Each probe used:

```text
/tmp/yulang2-oracle-target/debug/yulang --no-prelude --no-cache dump <source-file> --poly
```

The captured source inputs and hashes are:

| File | Source | SHA-256 |
| --- | --- | --- |
| `/tmp/yulang2-shadow-oracle-cases/identity.yu` | `my f x = x` | `6fdaa7a0ce83d2309290787aa7de9f1d9080bacf3f33726ac19974fc954a1273` |
| `/tmp/yulang2-shadow-oracle-cases/compose.yu` | `my compose f g x = f (g x)` | `4f0afebb4d341f374805e78bdd6bee2b93abee42343100ff61f89ae261186e8a` |
| `/tmp/yulang2-shadow-oracle-cases/captured_step.yu` | `my apply f = { my step x = f x; step }` | `d05809782dce91cb83886e4d80da87a5a3a145d3518b1cfdec2da2d3ce64658c` |

## Frozen Oracle observations

For `my f x = x`, the CLI emitted:

```text
my d0:f: 'a -> 'a = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
```

For `my compose f g x = f (g x)`, it emitted:

```text
my d0:compose: ('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0 = e7:(fn p0:d1:f -> e6:(fn p1:d2:g -> e5:(fn p2:d3:x -> e4:(e0:r0:f->d1:f e3:(e1:r1:g->d2:g e2:r2:x->d3:x)))))
```

For the exact captured-`step` candidate, it emitted:

```text
my d0:apply: ('a -> ['b] 'c) -> 'a -> ['b] 'c = e6:(fn p0:d1:f -> e5:block { let my p1:d2:step = e3:(fn p2:d3:x -> e2:(e0:r0:f->d1:f e1:r1:x->d3:x)); e4:r2:step->d2:step })
```

These are source compatibility observations from one exact old revision. They
do not show that current Yulang3 accepts the latter two programs, nor that
the current shadow's pending application premises have corresponding solved
types.

## Differential boundary

The default-off current F5 differential presently executes common leaf source
through current HIR, collection and solving, but exposes source provenance
rather than a Function scheme. Current `SolvedModule` has no public
`scheme_for`; public projections map Function values to `Unknown`, while
crate-internal tests can inspect finalized scheme views. The old printed
`'a -> 'a` can therefore guide a focused internal shape comparison, but
variable spelling and the full old-to-new scheme mapping need independent
normalization. No direct textual equality is claimed. Ordinary application
has no current production F5 path, so the old `compose` and `apply` outputs
remain baseline-side evidence only.

The previous statement “no executable old-infer runner exists” is narrowed:
stale, unverified artifacts and an April private `yulang-infer-playground`
are not the frozen Oracle; the executable above is newly built from the
verified frozen commit. The private playground remains a different system.

## Scope, costs and omissions

One bounded package build used one Cargo process, two jobs and 1 minute 26
seconds. Three tiny CLI processes handled the listed inputs. This was
functional source characterization, not performance measurement. No source
or manifest under the frozen commit was changed, and no expected result or
production behavior was modified. The temporary build/worktree live outside
the active checkout; they are environment artifacts, not repository inputs.

Unverified: current successor scheme equality; legacy full constraints versus
public display; annotations/effects on broader programs; source-formation
soundness, principality, source adequacy; current Yulang3 production
acceptance and all-view inference replacement.
