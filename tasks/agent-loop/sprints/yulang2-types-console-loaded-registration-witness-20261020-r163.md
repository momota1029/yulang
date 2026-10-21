# Yulang2 loaded-registration witness continuation — R163

Status: exact fresh-output and capture contract. The resumed goal continues unchanged Types/Console source correspondence. R162's observer now compiles, but its Types capture timed out at 60s after emitting a valid JSONL prefix into the exclusive R160 path. R163 retains that prefix and uses a reviewed fresh allowlist in a new copied candidate. No tests or runtime execution are included.

## Outcome and parent gates

Authenticate useful complete loaded-file records already present in R162's partial output, then capture complete registration streams for unchanged Types and Console samples—or record a precise bounded obstruction. Apply the records to R152–R154 to locate the actual census/order premise. Keep source identity, complete observer capture, accepted static inference, runtime behavior, and parent theorem closure distinct. R149 Types and host-output claims remain unchanged. All Simple-sub/evaluator A/B, source/native, runtime, and production gates remain OPEN.

## Frozen prefix and exact input identities

- R162 partial Types output: `/tmp/yulang2-r160-observer/out/types.jsonl`, SHA-256 `413fd2e4a260f9a16b5a58b811cf391f349ded5095c09a9eccfd38992a279eda`, 730 valid JSONL lines. It contains 41 `loaded_file` records and 689 `registration_event` prefix records, ending at ordinal 729. Treat registration events as incomplete; do not call this a witness.
- R162 binary SHA-256 `302c06e00dcb683471e670c55df359419ae6bd2eae2c75678a87642c3fa7df60`; build status 0. R162 Types capture status 124 at 60s; stdout/stderr empty. R161/R162 scratch and partial output are immutable and must not be cleaned or overwritten.
- Exact input samples remain `/tmp/yulang2-r161-witness/input/Types.yu` (SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`) and `Console.yu` (`ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`). Exact 40-file stdlib closure manifest SHA-256 `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- R162 loaded Types source has the deterministic prefix `use std::prelude::*\nmod std;\n` followed by exact Types input bytes. The source lane will verify this relation, all 40 library source hashes, byte lengths, token concatenation, byte spans, balanced CST enter/leave events, and the partial registration event boundary.

## Exact candidate correction and allowlist

- Base Y2 commit remains `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Fresh archive `/tmp/yulang2-r163-observer/oracle/` is R162's reviewed candidate plus only two string-constant path changes in `crates/sources/src/lib.rs`. No other file may differ from R162.
- R162 sources hash `0e3f296daa52fae921c6489fb5b85d98aca86992203bfa87fce913729266c6c8`; R163 corrected `sources/src/lib.rs` hash `b73cc664f01757f2fa29a8b67f260edbde782ea586719c8fef17005d3b76ff6a`.
- Frozen `module_map/mod.rs` SHA-256 `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; `module_map/finish.rs` `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`; Cargo.lock `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- Fresh exclusive output allowlist: `/tmp/yulang2-r163-observer/out/types.jsonl` and `/tmp/yulang2-r163-observer/out/console.jsonl`. Both are absent now. Never write to R160 outputs or R161/R162 scratch. Each output is created only by the observer with exclusive-create; preserve partial files.

## Fresh scratch and exact commands

R163 Cargo home is copied from the reviewed R162 offline cache at `/tmp/yulang2-r163-witness/cargo-home/`; new target, temporary and receipts are `/tmp/yulang2-r163-witness/target/`, `tmp/`, and `logs/`. Cargo-generated files only under target; compiler/linker temporary files under tmp; receipts only in logs. Inputs and candidate archive are read-only after review. No repo, original Cargo home, rustup toolchain, or R161/R162 scratch writes.

After independent CLEAN review, Luna issues a fresh grant: one offline locked build (one Cargo process/job, 480s wall timeout) followed, if successful, by two static capture processes serially, up to 300s each (600s total). The new 300s per-sample bound is a deliberate bounded increase after the observed 60s timeout, not a completion estimate. Maximum new scratch data is 8 GiB across cargo-home/target/tmp/logs. Preserve generated inventories. No automatic repair, retry, dependency download, or cleanup.

Build exactly once:

```sh
CARGO_HOME=/tmp/yulang2-r163-witness/cargo-home \
CARGO_TARGET_DIR=/tmp/yulang2-r163-witness/target \
TMPDIR=/tmp/yulang2-r163-witness/tmp \
CARGO_BUILD_JOBS=1 \
cargo build --offline --locked \
  --manifest-path /tmp/yulang2-r163-observer/oracle/Cargo.toml \
  -p yulang
```

If build succeeds, capture Types and Console serially with their respective R163 output paths:

```sh
YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r163-observer/out/types.jsonl \
/tmp/yulang2-r163-witness/target/debug/yulang \
  --no-cache --std-root /tmp/yulang2-r161-witness/lib \
  dump-poly-std /tmp/yulang2-r161-witness/input/Types.yu
```

Then use output `/tmp/yulang2-r163-observer/out/console.jsonl` and input `/tmp/yulang2-r161-witness/input/Console.yu`. Use a 300s timeout for each. After a Types timeout, Console may proceed only after process cessation is confirmed, its inputs/dependencies are unchanged, and the failure is isolated to that invocation; never rerun Types. Stop both captures for observer/schema/provenance failure. `dump-poly-std` is static lowering/source evidence only; it neither evaluates the samples nor observes host writes. No tests or `run-mono-std`.

## Lanes, resources, review, and stop conditions

Source/proof lane (180s): authenticate the R162 loaded-file identities and structural properties; apply R152–R154 only within their premises; state exactly what partial registration prefix does and does not establish. Implementation/capture lane: change only the two output path constants, then one fresh build and two serial captures. Independent review checks source/API/output pins, the exact two-string delta, all loaded-record/source relations, record completeness, provenance/order, command bounds and evidence separation.

Fresh R163 cap 1,800 seconds, Astra 0, no carryover: allowlist correction/input packet 120 + prospective review 120 + one build 480 + two captures 600 + source-certificate application 180 + independent evidence review 180 + closeout 120. Initial ledger after packet preparation: 120 charged, 1,680 reserved. Stop on any hash mismatch, existing output, offline build failure, timeout not allowed by the conditional rule, observer/schema/provenance failure, or 8 GiB/other stated bound. Preserve all logs and partial outputs. No parent gate closes from compilation or partial/complete records alone.
