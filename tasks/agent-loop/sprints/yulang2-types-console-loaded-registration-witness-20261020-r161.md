# Yulang2 loaded-source/registration witness — R161

Status: revision 2, prospective exact invocation contract. The active goal provisionally adopts unchanged Types/Console samples and continued source-to-execution research. This sprint is authorized for exact input and invocation preparation plus independent review. The build and static source captures below remain conditional: Luna must record a separate execution grant after the user explicitly authorizes these exact commands. No test suite, Y3 edit, expected-output change, or production cutover is authorized.

## Outcome and parent status

Collect the exact unchanged Y2 Types and Console source bytes through the pinned R160 provisional observer, using the no-cache source route and exactly the pinned 40-file stdlib closure. Apply the resulting static source/lowering records to the reviewed R152–R154 relations to find the first actual declaration-census/order premise. This is a finite source witness only. It does not establish runtime behavior, successful Y3 compilation, evaluator correspondence, the original Simple-sub/evaluator A/B theorems, soundness, principality, or production readiness. All those gates remain OPEN.

## Immutable inputs and current scratch preparation

- Y2 oracle commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Source template owner: `web/playground/src/main.ts`, blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`, SHA-256 `baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90`.
- Types template: 142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Console template: 92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`.
- Standard-library closure: exact 40 `lib/std/**` path/blob entries in `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`, closure SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`. Luna copied and Git-blob-verified each file against the pristine R160 archive.
- Prepared library path/hash manifest: `/tmp/yulang2-r161-witness/logs/lib-manifest.txt`, SHA-256 `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- R160 static observer contract: SHA-256 `3901728bb019ddec1a1641014ce7884fbadd036597e741fcdc9e6f0f83959553`.
- R160 exact correction packet: SHA-256 `c1b3cfdbb2949f37b9787b9ba5fd7edf15afb7a93ed67369ccfdbaaa117d5bb0`.
- R160 independent static code/path review: `notes/progress/2026-10-20-r160-code-review.md`, SHA-256 `674544376404a4c7f40124cefccd743e0841eb0ef01621c1999c5975ea983540`.
- R160 candidate source hashes: sources `b8e3b93046f09f5b5fa0ec26de84879b1da20719b899c6c2ca784532e2df1c69`; module_map `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; finish `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`.
- Frozen source archive: `/tmp/yulang2-r160-observer/oracle/`; it must not be edited for R161.
- Prepared sample inputs and library: `/tmp/yulang2-r161-witness/input/{Types,Console}.yu` and `/tmp/yulang2-r161-witness/lib/`; the two sample hashes/byte lengths and all 40 source blob pins were verified during preparation.
- Cargo.lock SHA-256: `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- Read-only global Cargo linker config: `/home/momota1029/.cargo/config.toml`, SHA-256 `ae913eabcfcdcd3c0c22c27c76397f859176c914eae0686b183d68d5b94776e9`; it selects clang and mold. Cargo 1.95.0 and rustc 1.95.0 are installed; rustup toolchain files remain read-only at `/home/momota1029/.rustup/`.
- Offline Cargo state was copied, excluding credentials and binaries, to `/tmp/yulang2-r161-witness/cargo-home/`: registry index (~49 MB), crate cache (~82 MB), unpacked sources (~341 MB), Git checkouts (~20 MB), and Git DB (~4.4 MB), plus the pinned linker config. All future Cargo cache writes stay inside this temporary home.
- The one Cargo invocation's generated target tree is scoped to `/tmp/yulang2-r161-witness/target/`, owned by Luna only for this invocation. Cargo-generated contents only; no worker or follow-up process may edit arbitrary files there. Use `/tmp/yulang2-r161-witness/tmp/` as `TMPDIR` for compiler/linker temporaries and `/tmp/yulang2-r161-witness/logs/` for captured receipts. Cargo home, target, tmp, logs, and the two allowlisted observer outputs are the only write locations; source inputs are read-only. Do not write to the repository, original Cargo home, or rustup toolchain. The build is bounded to one Cargo process, 480 seconds, one Cargo build job, and 8 GiB maximum new scratch data across cargo-home/target/tmp/logs; stop at the first bound. Preserve inventory and receipts. Cleanup is not authorized by this packet.
- At packet preparation, neither R160 observer output file nor its parent `out/` directory exists. After an explicit execution grant only, create that empty directory; never create or alter either JSONL file except through the observer's exclusive-create operation.

## Conditional build and exact sample commands

The static reviewer must check this invocation packet, observer allowlist, source identity and all paths before Luna requests the separate execution authorization. If authorized, run one heavy Cargo process at a time, with no retries:

1. Recheck the prepared input/library manifest, lockfile, observer source hashes, output-file absence, and scratch paths. Create only the missing empty output directory. Do not copy or modify further Cargo inputs. Cargo build outputs use `CARGO_TARGET_DIR=/tmp/yulang2-r161-witness/target/`; Cargo cache and linker config use the prepared temporary home. Installed rustup toolchains remain read-only under `/home/momota1029/.rustup/`.
2. Perform one build only:

   ```sh
   CARGO_HOME=/tmp/yulang2-r161-witness/cargo-home \
   CARGO_TARGET_DIR=/tmp/yulang2-r161-witness/target \
   TMPDIR=/tmp/yulang2-r161-witness/tmp \
   CARGO_BUILD_JOBS=1 \
   cargo build --offline --locked \
     --manifest-path /tmp/yulang2-r160-observer/oracle/Cargo.toml \
     -p yulang
   ```

3. Record the built binary hash. Before each invocation verify the exact input and library manifest hashes. The observer only accepts these R160 output paths:

   - `/tmp/yulang2-r160-observer/out/types.jsonl`
   - `/tmp/yulang2-r160-observer/out/console.jsonl`

   Exclusive `create_new` applies. If either output file already exists, stop and preserve it; never truncate, delete, append, or retry. If creation fails, retain stderr and mark the witness invalid.

4. Run two serial, source-only dump processes with the built binary. `dump-poly-std` emits lowering/source observer records; it does not evaluate either sample or execute host writes. These captures therefore cannot establish or refute the expected host payloads. Runtime output claims `(42, Yulang)\n`, `hello from Yulang\n`, and `3\n` remain unobserved and require a separately authorized runtime witness using the distinct `run-mono-std` route.

   ```sh
   YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r160-observer/out/types.jsonl \
   /tmp/yulang2-r161-witness/target/debug/yulang \
     --no-cache --std-root /tmp/yulang2-r161-witness/lib \
     dump-poly-std /tmp/yulang2-r161-witness/input/Types.yu
   ```

   Then repeat with output `/tmp/yulang2-r160-observer/out/console.jsonl` and input `Console.yu`. Do not parallelize. Capture exact argv, environment allowlist, stdout, stderr, exit status, binary hash, source pins, full JSONL and any partial output under `/tmp/yulang2-r161-witness/logs/`. Do not claim success from CLI status alone.

The expected static oracle claims are fixed by the authoritative R149 design: Types public entries include polymorphic `id`, `answer: int`, `name: str`, and `pair: (int, str)`. A mismatch in these source/lowering records is evidence against this finite static sample claim, not permission to alter source or expected output. Runtime payload expectations stay fixed in R149 but are outside the evidence produced by these commands.

## Source-certificate application and independent evidence review

After successful capture, Luna uses 120 seconds to join exact loaded bytes, module/band identities (including explicit anonymous-unavailable cases), initial operator state, CST, and all twelve ordered source registration events. Apply only R152–R154 relations within their stated premises. Identify the first actual census/order/classification gap. Independent reviewer (120 seconds) checks omitted/duplicated records, wrong source route, stale/mixed files, identity/provenance, diagnostic behavior, static output claims, commands and raw artifact hashes. CLI success alone is insufficient. Host runtime effects remain unobserved by this sprint.

## Conditional resources and current authorization

Fresh R161 cap 1,200 seconds: input/command packet preparation 120 + prospective review 120 + conditional single offline build 480 + conditional two serial source captures 120 + source-certificate application 120 + independent evidence review 120 + closeout 120. Astra 0; no R160 carryover. The unissued build/capture/application/evidence-review/closeout allocations total 960 seconds; the 120-second preparation and 120-second prospective review are charged/reserved separately. No test suite is included. No build or sample invocation has occurred. Luna will issue execution grants only after the packet is independently CLEAN and the user explicitly authorizes the exact build and captures.

## Stop conditions

Stop before command execution if the user authorization is absent; any source/input/library/lock hash differs; output files already exist; Cargo cannot operate offline with the frozen cache; the pinned binary path differs; observer failure appears; a source/module/band join contradicts the reviewed schema; or time/CPU/scratch bounds are reached. Preserve all logs, partial records and generated artifact inventory. No automatic repair, retry, cleanup, code edit, expected-output change, theorem closure, or production promotion follows.
