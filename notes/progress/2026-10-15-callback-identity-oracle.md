# Callback Hygiene through ordinary identity: frozen Oracle observation

Date: 2026-10-15
Status: finite reference inference/execution succeeded; independent provenance review found no findings
Authority: [direct identity decision](../design/2026-10-15-callback-identity-forwarding.md)
Native baseline: `3df337fb06cae49164cc90351f274751bf830200`
Frozen Oracle: clean detached `a58eefc31e22141574b6f20c6a5748151c6d79f1`

## Exact discriminator and result

The [executed variant](../../tools/inference-playground/oracle/callback-hygiene-identity.yu)
changes only the [original source](../../tools/inference-playground/oracle/callback-hygiene.yu)
by inserting `my id x = x` before `g` and replacing the loop's `h i` with
`id (h i)`. Reversing those two mutations reproduces the original bytes.
Comments, imports, nested handlers, loop, callback, output and tail remain intact.

The single process exited 0. Its complete stdout was:

```text
type g: (int -> ['a] any) -> ['a] int
Out 1: 0
run roots [()]
```

The type and root lines are wrapper observations; the program writes only
`Out 1: 0`. Stdout and stderr are byte-identical to the previously executed
original. That original run was reused for comparison, not repeated.

The [existing wrapper and public compact web route](2026-10-15-exact-callback-hygiene-oracle.md#actual-execution-route)
were reused unchanged: real embedded std, source-to-poly and readiness checks,
control lowering, evidence plan and evidence VM. No fake std, edited Oracle
source, alternate backend or full-std fallback was used. The frozen Oracle
working tree was clean before and after execution.

## Reproduction and bounded verification

Command:

```text
/tmp/yulang-callback-exact-20261015/compact-driver /tmp/yulang-callback-identity-20261015/callback-identity.yu
```

The observation directory contains the source, copied guard `observe.py`,
stdout/stderr, `manifest.json` and frozen producer `REPORT.md`. The existing
driver, linked libraries and source pins are documented in the original-run
record. This run checked the original source, wrapper and executable pins before
launch and the executable hash again afterward.

| Artifact | SHA-256 |
| --- | --- |
| Identity source | `1152f84a824bf13fca4c2aa1e10a3d788c8049ad162fcf2be7eb7ebb9da9190f` |
| Executable | `1ff46aa60505491cae24c0764fa3914cd7c2e5d27caef6a9f4f5cda738da2b2f` |
| Guard | `52695e5e9e22f3f5aa98455a62688fa8069e0f4550e234c84ac866954ca0a03f` |
| Stdout | `eb3d3b8e30e3f1873b107eb93467f1f889acc664a7a1e0bac81282ac7e98eef8` |
| Manifest | `99e437bfd0fab8d86b7442f1e98289e0b084aa4a7b869b6b572713bdbfeac1bc` |
| Producer report | `3790aa73a2012c3475b1bc85701342611861546b3a99d297bfce0916d23ed976` |

The previously reviewed corrected envelope was retained: 90 s wall, 60 s CPU,
4 GiB address space, 2 GiB sampled RSS, 256 KiB combined stdout/stderr,
100 ms polling, isolated process group and zero core size. No process-wide
file-size limit was introduced. Only the child's environment sets
`YULANG_CACHE_DIR=/dev/null/yulang-callback-oracle-cache`, retaining cold source
construction and the actual API's tolerated cache-write failure.

One process, one source, no repetitions or builds. Observed wall time was
35.876 s; user/system CPU 35.067/0.544 s; sampled peak RSS 602,247,168 B.
No guard triggered and no output was truncated. Sampling can miss short peaks.

This verifies the selected finite reference example. It does not establish
native identity preservation, generalized source coverage, principality,
the receiver construction or a universal hygiene/soundness theorem.

M2 used one independent spec auditor for the source mutation, hashes, execution
provenance, guards and claim boundaries. Review found no findings; it reused
the previously reviewed wrapper/library internals. No native tests or builds,
browser-equivalence check or general proof certification was performed.
