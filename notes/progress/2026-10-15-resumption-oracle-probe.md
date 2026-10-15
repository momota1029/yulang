# Resumption discriminator: unsuccessful frozen Oracle observation

Date: 2026-10-15
Status: one bounded observation stopped during poly lowering; no execution result
Branch: `research/simple-sub-intrusion`
Frozen Oracle: clean detached `a58eefc31e22141574b6f20c6a5748151c6d79f1`

## Source and scope

The native computation-laziness test admits a source skeleton with pause inside
the delayed argument, a relay io handler, and an outer keep handler resuming the
raw continuation. This observation attempted the following layout spelling with
real std, an additional outer io handler and explicit printing:

```yu
use std::*

act io:
    our tick: int -> int
act pause:
    our stop: int -> int

my relay(thunk: [io] int) = catch thunk:
    io::tick(p), _ -> 1
    v -> v

my keep(thunk: [pause] int) = catch relay thunk:
    pause::stop(p), k -> k 0
    v -> v

my result = catch keep {
    my ignored = pause::stop 0
    io::tick 1
}:
    io::tick(p), _ -> 2
    v -> v
result.say
```

The native test and this source are not byte-identical. No successful
cross-version elaboration correspondence is claimed. In particular, neither
return value 1 nor 2 was selected as an expected result: a missing pre-query
receipt prevents the current conditional source argument from predicting this
case. This is distinct from the later relay-body-pause discriminator.

The unchanged [compact Oracle wrapper](../../tools/research_callback_hygiene_oracle.rs)
reported `catch arm is missing a body expression` and stopped at its poly-error
gate. Exit was 1, stdout empty. Control lowering and VM execution were withheld;
the failed lowering does not identify a runtime hygiene defect. No rerun,
source repair, full-std fallback or executable rebuild was performed.

## Provenance and budget

Observation directory: `/tmp/yulang-resumption-discriminator-20261015`.
Command, with cwd `/tmp/yulang-hygiene-audit-my68a_85/oracle`:

```text
/tmp/yulang-callback-exact-20261015/compact-driver /tmp/yulang-resumption-discriminator-20261015/resumption-discriminator.yu
```

The guard ran under `python3`. A preceding shell invocation of unavailable
`python` exited 127 before launching either the guard or the Oracle; it is not
an additional Oracle observation. The Oracle tree was clean before and after.
The source and executable hashes matched before and after the actual process.

| Artifact | SHA-256 |
| --- | --- |
| Source | `45f3f297af007b665660d591f3a6e3e54247504481c0d61544a9689d8e02e633` |
| Executable | `1ff46aa60505491cae24c0764fa3914cd7c2e5d27caef6a9f4f5cda738da2b2f` |
| Guard | `322e2b4c5ab9f18d6c23d8589f47f5ee63273848ff342bcc1904226f902f7039` |
| Stderr | `7437703761ec5f60f6eb2edeee698e331f98b550a652951ca779ed28397bb36b` |

One process, one source, no repetitions or builds. The prior reviewed envelope
was reused: 90 s wall, 60 s CPU, 4 GiB address space, 2 GiB sampled RSS,
256 KiB combined output, 100 ms polling, isolated process group, unexpected-child
guard, zero core size, no process-wide file-size limit. Child-only cache override:
`YULANG_CACHE_DIR=/dev/null/yulang-callback-oracle-cache`.

Observed wall time was 35.241 s; user/system CPU 34.734/0.488 s; sampled peak RSS
602,198,016 B. No guard triggered; stdout/stderr sizes were 0/149 B, untruncated.
This is one finite unsuccessful source observation, not a performance benchmark
or a result for the already successful original/identity Callback Hygiene runs.

Independent provenance review found no findings in the exact source, hashes,
guard, manifest, failure and claim boundaries. It did not investigate the
lowering error's root cause or certify historical tree cleanliness. No native
build, broad suite, browser execution or soundness certification was performed
for this observation.
