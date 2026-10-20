# R161 witness packet — unchanged Yulang2 Types and Console

Status: frozen exact input/invocation packet for independent prospective review. Packet preparation copied and hash-verified inputs only. No build, test, parser/sample execution, observer output, or Y3 write occurred. Conditional build/captures require a separate exact user authorization after this review.

## Identity and dependency pins

- Contract: `tasks/agent-loop/sprints/yulang2-types-console-loaded-registration-witness-20261020-r161.md` (rev1; hash in `current.json`).
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

All Cargo writes must stay under:

- Cargo home/cache: `/tmp/yulang2-r161-witness/cargo-home/`
- Cargo target/build output: `/tmp/yulang2-r161-witness/target/`
- stdout, stderr, status, command/environment receipts: `/tmp/yulang2-r161-witness/logs/`
- exact inputs/library: `/tmp/yulang2-r161-witness/input/` and `/tmp/yulang2-r161-witness/lib/`
- observer outputs (through exclusive observer creation only): the two R160 allowlisted JSONL paths above.

## Conditional commands — not authorized or run

After explicit user authorization and a separate Luna execution grant only, recheck all hashes, output absence, and exact paths. Do not run a test suite. Use one build process and serial sample invocations, with no retry.

Single offline locked build:

```sh
CARGO_HOME=/tmp/yulang2-r161-witness/cargo-home \
CARGO_TARGET_DIR=/tmp/yulang2-r161-witness/target \
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

Expected finite observations from the adopted R149 specification:

- Types pane includes polymorphic `id`, `answer: int`, `name: str`, `pair: (int, str)`; host write is `(42, Yulang)\n`.
- Console host writes, in source order: `hello from Yulang\n`, then `3\n`.

A mismatch is recorded as a counterexample/obstruction to this finite sample claim. It never permits rewriting source, expected output, or semantics.

## Review and stop conditions

Independent reviewer checks sample bytes, exact 40-file closure, manifest/Cargo cache/build paths, R160 pins and output allowlist, source-only `--no-cache` route, one-process ordering, raw capture expectations, and stop behavior. A CLEAN packet review does not authorize the commands. Stop before execution if user authorization is absent, any pin differs, either output exists, Cargo cannot resolve offline, the binary path differs, or the observer reports failure. Preserve partial evidence. No automatic repair/retry, theorem closure, or production promotion follows.
