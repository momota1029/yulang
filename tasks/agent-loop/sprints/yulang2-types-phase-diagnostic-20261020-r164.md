# Yulang2 Types phase-localization diagnostic — R164

Status: proposed fresh bounded diagnostic continuation of the resumed inference/evaluator goal. No command is authorized until the exact packet receives CLEAN independent review and Luna records a fresh grant. Baseline Y2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`; original Types/Console expectations and Simple-sub/evaluator A/B quantifiers remain unchanged and OPEN.

## Outcome and diagnostic question

Use the already built, hash-pinned R163 observer binary with its observer-output environment variable unset and existing `YULANG_INFER_TIMING=files` telemetry enabled for one Types `dump-poly-std` invocation. Determine the last reported phase and per-file body-lowering boundary within 120 seconds. This distinguishes a phase-localized slowdown from work specific to observer serialization after the same Types capture produced the identical 730-record hash at R162's 60-second and R163's 300-second bounds. Telemetry is diagnostic evidence only: absence of a completion marker proves neither nontermination nor a compiler defect.

No new instrumentation, build, observer capture, retry, Console run, test, runtime execution, semantic change, production promotion, or theorem closure is included. Source identity, complete registration/census, accepted inference, evaluator behavior, host output and parent theorem gates remain OPEN.

## Frozen inputs and dependencies

- R163 frozen candidate archive: `/tmp/yulang2-r163-observer/oracle/`.
- Candidate source observer file: `crates/sources/src/lib.rs`, SHA-256 `b73cc664f01757f2fa29a8b67f260edbde782ea586719c8fef17005d3b76ff6a`.
- Existing timing implementation: `crates/infer/src/lowering/body/mod.rs`, SHA-256 `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1`. `YULANG_INFER_TIMING=files` prints phase labels and each loaded file's lower start/done around the body-lowering loop.
- Reused binary `/tmp/yulang2-r163-witness/target/debug/yulang`, SHA-256 `ce3284bcbeb9d71ed14988587b50be286dbd66733d1e37dc9e66e6a17a79850c`; the R163 offline build receipt identifies this candidate. No rebuild.
- Types input `/tmp/yulang2-r161-witness/input/Types.yu`, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Standard-library root `/tmp/yulang2-r161-witness/lib`; manifest `/tmp/yulang2-r161-witness/logs/lib-manifest.txt`, SHA-256 `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- R163 contract SHA-256 `e3f6db10990b9e791402e186a3f5dbbc2bfff543dca4593baa765309fb0a11e0`; R163 closeout `notes/progress/2026-10-20-r163-closeout.md`, SHA-256 `068d63cfb4b1cb05d5b371dc1ae74daabafb08d239ab96992cdaf9c009095bd4`; R162 loaded-file audit SHA-256 `22742c3e451cc195c717c868cb57e0e24760cf3b6bccc1a9a7063174545f1a6e`.

The dispatcher suggested an abbreviated timing-source hash that does not match the frozen candidate; this packet pins and uses the verified archive file hash above. No source archive is changed.

## Exact output allowlist and command

The only invocation outputs are new files under `/tmp/yulang2-r164-diagnostic/`:

- `types.stdout`
- `types.stderr`
- `types.status` (decimal process status plus newline)

The directory and all three files must be absent before starting. Preserve them after the single invocation. The command is issued once, after review:

```sh
mkdir -p /tmp/yulang2-r164-diagnostic
set +e
timeout --signal=TERM --kill-after=5s 120s \
  env -u YULANG_LOADED_WITNESS_OUT YULANG_INFER_TIMING=files \
  /tmp/yulang2-r163-witness/target/debug/yulang \
  --no-cache --std-root /tmp/yulang2-r161-witness/lib \
  dump-poly-std /tmp/yulang2-r161-witness/input/Types.yu \
  > /tmp/yulang2-r164-diagnostic/types.stdout \
  2> /tmp/yulang2-r164-diagnostic/types.stderr
status=$?
printf '%s\n' "$status" > /tmp/yulang2-r164-diagnostic/types.status
```

No other files or paths may be written. A timeout status is recorded as a bounded obstruction. Never rerun, extend the timeout, or start Console within R164.

## Lanes, resources and gates

Fresh cap 960 seconds, Astra 0, no carryover: packet preparation 120 + independent prospective review 120 + conditional single diagnostic 120 + source/proof application 360 + independent evidence review 120 + closeout 120 = 960. Reserve and charge the full grant when issued. Keep implementation diagnostic and source/proof analysis on disjoint exact output paths; no source changes.

- Luna diagnostic lane: one bounded Types invocation, capture exact stdout/stderr/status and command/input/binary hashes, then stop.
- Source/proof lane: apply authenticated Types loaded-file/CST evidence to R152–R154's constructor/publication relations; map emitted telemetry only to the exact phase/file owner proven by the pinned candidate source. Keep incomplete registration, anonymous ancestry, sample census and accepted inference distinct.
- Independent review: verify exact command/environment, pins, output hashes/status, telemetry semantics and each source-level phase interpretation. An absent marker cannot be promoted to a claim of nontermination.

Stop on any hash mismatch, unexpected write, output preexistence, contradictory telemetry, source/command mismatch or 120-second bound. Preserve prior R161–R163 scratch and artifacts. The next material consultation trigger is a phase-localized obstruction, new safe implementation seam, authority/resource change or sprint boundary.

## Parent claim and review boundary

R164 can localize one diagnostic route only. It cannot establish a complete registration/table census, accepted static inference, Types/Console runtime behavior, source/native correspondence, Simple-sub/evaluator A/B theorem, expected host output or production readiness. Any beyond-contract source instrumentation requires a separately reviewed contract revision and fresh authority.
