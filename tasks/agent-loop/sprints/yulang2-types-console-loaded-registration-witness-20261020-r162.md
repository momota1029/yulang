# Yulang2 loaded-registration witness correction — R162

Status: exact correction and capture contract. The active goal resumes the same unchanged Types/Console sample witness. R161's offline build stopped at a statically reviewed observer type error; R162 changes one observer expression in a fresh archive, then requires independent review before one new build grant. No test suite or runtime execution is included.

## Outcome and preserved parent claims

Compile the pinned R160 observer candidate with the narrow `BString` serialization correction, then capture its static source/lowering records for the unchanged Y2 Types and Console inputs. Apply those records to R152–R154 to find the first actual declaration-census/order premise. This does not establish host effects, runtime behavior, Y3 compilation, evaluator correspondence, Simple-sub/evaluator A/B closure, soundness, principality, or production readiness. All parent gates stay OPEN.

R149 expected Types entries and runtime host payload `(42, Yulang)\n`, plus Console runtime writes `hello from Yulang\n` then `3\n`, remain unchanged. `dump-poly-std` cannot observe or refute those runtime payloads.

## Exact baseline, correction, and inputs

- R160 candidate archive source: `/tmp/yulang2-r160-observer/oracle/`; pinned Y2 base commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Fresh R162 archive: `/tmp/yulang2-r162-observer/oracle/`. It differs recursively from the R160 candidate only at `crates/sources/src/lib.rs`.
- Frozen R160 candidate hashes: `sources/src/lib.rs` `b8e3b93046f09f5b5fa0ec26de84879b1da20719b899c6c2ca784532e2df1c69`; `module_map/mod.rs` `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; `module_map/finish.rs` `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`.
- R162 corrected `crates/sources/src/lib.rs` SHA-256: `0e3f296daa52fae921c6489fb5b85d98aca86992203bfa87fce913729266c6c8`. The only source delta is `String::from_utf8_lossy(symbol.as_ref())` to `String::from_utf8_lossy(symbol.as_str().as_bytes())`. The pinned `qp-trie 0.8.2` `src/wrapper.rs` hash is `25570d817a5af7f0e01359e3df6165c077cfa58d7fe9f7dc9b0a52cd4e87ec09`; `BString::as_str()` is public and returns `&str`.
- Lockfile SHA-256: `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- Exact unchanged sample inputs and 40-file library closure remain at `/tmp/yulang2-r161-witness/input/` and `/tmp/yulang2-r161-witness/lib/`; Types SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`, Console SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`, library manifest SHA-256 `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- R161 build failure receipt: Cargo status 101; stderr SHA-256 `4cd17b723afb2baf709b066b793f6f36a50b87a2411a2b5357aa343940e97c3b`. Its target/logs remain untouched.
- The exact observer output allowlist stays `/tmp/yulang2-r160-observer/out/types.jsonl` and `console.jsonl`; both remain absent. The observer must use exclusive-create. Never overwrite, append, retry, or clean them.

## Exact fresh scratch and command scope

R162 Cargo home is a fresh offline copy at `/tmp/yulang2-r162-witness/cargo-home/`; its input was the hash-verified R161 cache copy. New target, temporary and receipt paths are `/tmp/yulang2-r162-witness/target/`, `tmp/`, and `logs/`. Cargo-generated files only under target; compiler/linker temporaries under tmp; logs only in logs. Sample/library and archive inputs are read-only after review. No repository, original Cargo home, rustup toolchain, or R161 scratch writes.

Execution is a fresh grant only after CLEAN independent review: one Cargo process, one build job, 480-second wall timeout, at most 8 GiB new data across cargo-home/target/tmp/logs. Preserve final artifact inventory and receipts. No automatic repair, retry, dependency downloads, or cleanup.

## Conditional execution

After CLEAN review, Luna records the fresh execution grant. Recheck all source/input/manifest/lock hashes and both output files' absence. Create only missing empty target/tmp and already-absent output parent. Run exactly one build:

```sh
CARGO_HOME=/tmp/yulang2-r162-witness/cargo-home \
CARGO_TARGET_DIR=/tmp/yulang2-r162-witness/target \
TMPDIR=/tmp/yulang2-r162-witness/tmp \
CARGO_BUILD_JOBS=1 \
cargo build --offline --locked \
  --manifest-path /tmp/yulang2-r162-observer/oracle/Cargo.toml \
  -p yulang
```

If compilation succeeds, record the binary SHA and run serially once per input using the same source-only commands and R160 output paths as R161, with `YULANG_LOADED_WITNESS_OUT` selecting `types.jsonl` then `console.jsonl`, and `--no-cache --std-root /tmp/yulang2-r161-witness/lib dump-poly-std` on the matching sample. Do not run a test suite or `run-mono-std`. A second compile error stops this path and preserves evidence; no retry.

Successful build, valid observer record, and accepted static inference are separate outcomes. Static records do not evidence runtime host writes.

## Resources, review, and stop conditions

Fresh R162 cap 1,200 seconds, Astra 0: correction and exact packet 120 + independent correction/packet review 120 + one offline build 480 + two serial static captures 120 + source-certificate application 120 + independent evidence review 120 + closeout 120. R161's 1,200 seconds are spent; no carryover. Current R162 ledger begins at 120 charged and 1,080 reserved after preparation.

Independent correction/packet review checks the exact one-expression diff, `BString` API pin, archive comparison, sample/library/input pins, write scope, command/resource arithmetic, and evidence limits. After captures, independently check raw JSONL, ordered records, identities, and R152–R154 application. Stop on any hash mismatch, existing output, offline Cargo failure, first compiler error, observer failure, or resource bound. Preserve logs and partial artifacts. Do not infer runtime behavior, close parent theorems, or promote production.
