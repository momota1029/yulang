# R161 witness packet — unchanged Yulang2 Types and Console (revision 2)

Status: revised exact input/invocation packet for independent delta review. Packet preparation copied and hash-verified inputs only. No build, test, parser/sample execution, observer output, or Y3 write occurred. Conditional build and static source captures require separate exact user authorization after review.

## Identity and dependency pins

- Contract: `tasks/agent-loop/sprints/yulang2-types-console-loaded-registration-witness-20261020-r161.md` (rev2; hash in `current.json`).
- Y2 source owner commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- `web/playground/src/main.ts`: blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`, SHA-256 `baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90`.
- Exact sample inputs are `/tmp/yulang2-r161-witness/input/Types.yu` (142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`) and `Console.yu` (92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`). They match the full template strings, comments and trailing newline in the pinned Y2 source.
- The `--std-root` input is `/tmp/yulang2-r161-witness/lib/`, containing only the exact 40-file closure from `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`. Closure manifest SHA-256 is `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`. Each source's Git blob was verified against the pristine pinned R160 archive. The copied path/Git blob/file SHA inventory is `/tmp/yulang2-r161-witness/logs/lib-manifest.txt`, SHA-256 `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- `Cargo.lock` SHA-256 `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- R160 observer archive is immutable for this sprint: `/tmp/yulang2-r160-observer/oracle/`.
- R160 static candidate SHA-256: sources `b8e3b93046f09f5b5fa0ec26de84879b1da20719b899c6c2ca784532e2df1c69`; module map `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; finish `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`.
- The exact observer output allowlist is `/tmp/yulang2-r160-observer/out/types.jsonl` or `/tmp/yulang2-r160-observer/out/console.jsonl`. At preparation time the directory and both files are absent. After an execution grant, create only the empty parent directory. The observer must exclusively create the chosen file; if it exists, preserve it and stop without cleanup, overwrite, append, or retry.

## Cargo paths, cache and toolchain

No writes to the original Cargo home are allowed. The copied offline Cargo state is `/tmp/yulang2-r161-witness/cargo-home/`: registry index (~49 MB), crate cache (~82 MB), unpacked crate sources (~341 MB), Git checkouts (~20 MB), Git DB (~4.4 MB), and linker config. Credentials and executable binaries were excluded. The copied `config.toml` SHA-256 is `ae913eabcfcdcd3c0c22c27c76397f859176c914eae0686b183d68d5b94776e9`; it selects clang and mold. Installed Cargo/rustc are version 1.95.0; rustup toolchains under `/home/momota1029/.rustup/` are read-only.

The conditional one-process Cargo write scope is:

- Cargo home/cache: `/tmp/yulang2-r161-witness/cargo-home/`
- Cargo target/build output (Cargo-generated contents only, owned by Luna for this invocation): `/tmp/yulang2-r161-witness/target/`
- Compiler/linker temporary files: `/tmp/yulang2-r161-witness/tmp/` (`TMPDIR`)
- stdout, stderr, status, command/environment receipts: `/tmp/yulang2-r161-witness/logs/`
- exact inputs/library (read-only during execution): `/tmp/yulang2-r161-witness/input/` and `/tmp/yulang2-r161-witness/lib/`
- observer outputs (through exclusive observer creation only): the two R160 allowlisted JSONL paths above.

No writes to the repository, original Cargo home, or installed rustup toolchain. The build is bounded to one Cargo process, 480 seconds, one Cargo build job, and at most 8 GiB new scratch data across cargo-home/target/tmp/logs. Stop at the first bound. Capture the final artifact inventory and command receipts. This packet does not authorize scratch cleanup.

## Conditional commands — not authorized or run

After explicit user authorization and a separate Luna execution grant only, recheck all hashes, output absence, and exact paths. Do not run a test suite. Use one build process and serial sample invocations, with no retry.

Single offline locked build:

```sh
CARGO_HOME=/tmp/yulang2-r161-witness/cargo-home \
CARGO_TARGET_DIR=/tmp/yulang2-r161-witness/target \
TMPDIR=/tmp/yulang2-r161-witness/tmp \
CARGO_BUILD_JOBS=1 \
cargo build --offline --locked \
  --manifest-path /tmp/yulang2-r160-observer/oracle/Cargo.toml \
  -p yulang
```

Record the resulting binary hash. Then invoke the built binary directly once per sample, serially:

```sh
YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r160-observer/out/types.jsonl \
/tmp/yulang2-r161-witness/target/debug/yulang \
  --no-cache --std-root /tmp/yulang2-r161-witness/lib \
  dump-poly-std /tmp/yulang2-r161-witness/input/Types.yu
```

Repeat with `YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r160-observer/out/console.jsonl` and `Console.yu`. Capture exact argv, environment variable, stdout, stderr, exit status, binary hash, and full/partial JSONL. CLI exit code alone is not witness validity.

`dump-poly-std` emits lowering/source observer records; it does not evaluate either sample or execute host writes. These captures cannot establish or refute host payload expectations. Runtime claims `(42, Yulang)\n`, `hello from Yulang\n`, and `3\n` remain unobserved and require a separately authorized witness through the distinct `run-mono-std` route.

Expected static finite observations from the adopted R149 specification:

- Types pane includes polymorphic `id`, `answer: int`, `name: str`, `pair: (int, str)`.

The runtime output expectations remain fixed by R149, but are outside these commands' evidence.

A mismatch in the static records is recorded as evidence against this finite source/lowering sample claim. It never permits rewriting source, expected output, or semantics.

## Review and stop conditions

Independent reviewer checks sample bytes, exact 40-file closure, manifest/Cargo cache/build paths including target/tmp lease scope, R160 pins and output allowlist, source-only `--no-cache` route, one-process ordering, static capture expectations and runtime-evidence exclusion, resource arithmetic, and stop behavior. A CLEAN packet review does not authorize the commands. Stop before execution if user authorization is absent, any pin differs, either output exists, Cargo cannot resolve offline, a bound is reached, or the observer reports failure. Preserve partial evidence and generated artifact inventory. No automatic repair/retry/cleanup, theorem closure, or production promotion follows.
