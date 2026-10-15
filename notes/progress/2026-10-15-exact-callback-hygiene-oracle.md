# Exact Callback Hygiene: frozen web-route Oracle execution

Date: 2026-10-15
Status: exact original source inferred and executed on frozen Yulang2;
native Yulang3 completion and global soundness remain OPEN.
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.

## Target and result

The [retained source](../../tools/inference-playground/oracle/callback-hygiene.yu)
is the decoded **Callback Hygiene** template from frozen
`web/playground/src/main.ts:508–526`, including comments, imports, the original
lambda, loop, output calls and terminal expression. No source desugaring or
callback substitution was used for this Oracle execution.

Source SHA-256:
`9f6b445a2dc87e86448cf6e8cdba45a7af3ef9e6a76eec430df41f90e49e8385`.

The successful process exited 0. Its public scheme rendering was:

```text
type g: (int -> ['a] any) -> ['a] int
```

The program's only console output was `Out 1: 0\n`; root rendering was
`run roots [()]`. There was no intermediate `println` output. The type line
and root rendering are wrapper observations, not additional program writes.
This is finite Oracle evidence for the intended example, not a proof of its
scheme's principality or successor soundness.

## Actual execution route

The [standalone wrapper](../../tools/research_callback_hygiene_oracle.rs) links
the previously built, frozen Oracle libraries and calls:

1. `source_text_needs_full_embedded_std_for_playground` to check eligibility.
2. `build_poly_from_source_text_with_embedded_playground_std` on the unchanged
   text with filename `playground.yu`.
3. Lowering-error and `ensure_runtime_ready` checks; any error withholds execution.
4. `build_control_from_poly_output`, with its errors checked.
5. `evidence_vm::build_plan` and
   `run_program_with_plan_print_nth_label(..., "Out")`.

These are the actual compact-web inference/control/VM owners, identified in
Oracle `wasm/src/lib.rs:358–403,503,650,708`. Its compact standard profile is
the real web profile, not hand-selected fake std. Control/flow, range and
console use the original sources; other modules include profile-specific
definitions from `crates/yulang/src/playground_std.rs`. Full std is a different
input set. This wrapper does not reproduce web artifact caches, UI formatting,
or automatic full-std fallback; compact errors would stop explicitly.

Native public builders also attempt a disk-cache write. The successful child
used `YULANG_CACHE_DIR=/dev/null/yulang-callback-oracle-cache`: reads miss and
directory creation fails with ENOTDIR, an already tolerated cache failure.
Source construction still runs. This mirrors cold construction without disk
reuse; it does not bypass typing or runtime readiness. Owners are
`stdlib.rs:55–65`, `source/std_sources.rs:383–490`, and `cache.rs:3766–3803`.

## Reproduction and provenance

The original frozen build remains at
`/tmp/yulang-hygiene-audit-my68a_85/target/debug/deps`.
The wrapper was compiled once with `timeout 60s rustc --edition=2024`,
`-L dependency=<that directory>`, and these three `--extern` libraries:

| Library file | SHA-256 |
| --- | --- |
| `libyulang-41b7b66fe2aeddb3.rlib` | `c9901b70f1aeb40672079bc6ec12aa5183660ec2ea345b25ecb05d9c49d45eb3` |
| `libevidence_vm-a4defe861965a781.rlib` | `9a664f737a8039a75cd3dafa5c37851648645dbae395916d1de8bb2d81ec6c32` |
| `libpoly-878c74cab6a005c0.rlib` | `ab2cb05251904978ab4bb06f1f0befea3cb3577b05f5a8ea6cab13b4214c515a` |

Compiled wrapper source: `/tmp/yulang-callback-exact-20261015/compact_driver.rs`,
SHA-256 `c0682ca30cf7c0cb5dd3a4556e5794699331ee7e0423d2aa2ad4b143c30aa619`.
The archived wrapper differs only in correcting the header's cache comment.
Executable: `/tmp/yulang-callback-exact-20261015/compact-driver`, SHA-256
`1ff46aa60505491cae24c0764fa3914cd7c2e5d27caef6a9f4f5cda738da2b2f`.
It takes the original source file path as its sole argument.

The successful guarded command, input, environment, full log hashes and limits
are in `/tmp/yulang-callback-exact-20261015/compact-retry/manifest.json`.
The reusable observation scripts and all discarded-attempt logs are retained
in that parent directory. The successful stdout SHA-256 is
`eb3d3b8e30e3f1873b107eb93467f1f889acc664a7a1e0bac81282ac7e98eef8`.

## Measurement and abort accounting

This was bounded verification, not a benchmark. No warm-up or repetition was
performed for the successful route. The resource auditor established each
envelope before execution. Three compiler execution processes total:

| Route | Outcome | Wall time | Sampled peak RSS |
| --- | --- | --- | --- |
| CLI with full `oracle/lib` std | SIGKILL under 60 s CPU limit, no output; inconclusive | 60.202 s | 798,433,280 B |
| Compact wrapper, erroneous process-wide file-size guard | SIGXFSZ during cache write; invalid observation | 39.424 s | 602,513,408 B |
| Compact wrapper, corrected output-only guard and failed disk-cache destination | exit 0, inferred and ran | 36.229 s | 603,291,648 B |

All used 90 s wall, 60 s CPU, 4 GiB address space, 2 GiB sampled RSS, no core
dump, isolated process group and 100 ms polling. The corrected guard caps
combined stdout/stderr at 256 KiB and kills on excess or unexpected children.
The earlier `RLIMIT_FSIZE=256 KiB` also capped legitimate cache files; the
observed `.yucu.tmp` partial was exactly 262,144 bytes. Cache readers ignore
temporary names. No cache cleanup, limit escalation or semantic inference from
that signal occurred. One resource-reviewed corrective retry was authorized.

One wrapper compile/link process reused frozen libraries; there was no new
compiler build. UI/browser execution, native runtime, full std completion, and
general compatibility remain unverified. Related native source observations
are [separate evidence](2026-10-15-callback-identity-scope-observations.md), not
substitutes for the exact source executed here.

Independent conformance/provenance review passed after correcting that compact
profile source locator; no blocking/major findings. The native construction and
conditional tests have their own [checkpoint](2026-10-15-conditional-without-else.md).
