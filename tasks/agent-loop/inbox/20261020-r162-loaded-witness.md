# R162 exact correction and capture packet

Status: revision 3, frozen for independent final delta review. No R162 build, test, parser/sample command, observer output, or runtime execution has occurred. R161's build failure and scratch remain preserved.

## Frozen inputs and source delta

- Contract: `tasks/agent-loop/sprints/yulang2-types-console-loaded-registration-witness-20261020-r162.md` (SHA in `current.json`).
- Base Y2 commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Fresh archive: `/tmp/yulang2-r162-observer/oracle/`; recursive diff against `/tmp/yulang2-r160-observer/oracle/` contains exactly one file, `crates/sources/src/lib.rs`.
- Corrected file SHA-256 `0e3f296daa52fae921c6489fb5b85d98aca86992203bfa87fce913729266c6c8`; R160 source hash `b8e3b93046f09f5b5fa0ec26de84879b1da20719b899c6c2ca784532e2df1c69`.
- Correction replaces `symbol.as_ref()` with `symbol.as_str().as_bytes()` before `String::from_utf8_lossy`. Pinned qp-trie 0.8.2 `wrapper.rs` SHA-256 `25570d817a5af7f0e01359e3df6165c077cfa58d7fe9f7dc9b0a52cd4e87ec09` exposes `as_str() -> &str`.
- Other two candidate file hashes are unchanged: module map `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; finish `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`.
- Lockfile SHA-256 `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- R161 inputs remain immutable: Types `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`, Console `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`, exact 40-file library manifest `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`.
- R161 build stderr remains at `/tmp/yulang2-r161-witness/logs/build.stderr`, SHA-256 `4cd17b723afb2baf709b066b793f6f36a50b87a2411a2b5357aa343940e97c3b`; no R161 output file or binary exists.

## Conditional exact build and captures

The reviewer must adjudicate the one-line correction and exact paths before a fresh Luna grant. R162 Cargo home is `/tmp/yulang2-r162-witness/cargo-home/`; target `/tmp/yulang2-r162-witness/target/`; compiler/linker temporary directory `/tmp/yulang2-r162-witness/tmp/`; receipts `/tmp/yulang2-r162-witness/logs/`. All are fresh R162 paths. Use one Cargo process/job, 480-second wall timeout, and 8 GiB new scratch ceiling. Inputs are read-only. Preserve generated inventory; no cleanup or retry.

Build once with the exact command in the R162 contract. If it succeeds, run two serial `dump-poly-std` invocations on the pinned Types and Console inputs, with `--no-cache --std-root /tmp/yulang2-r161-witness/lib` and the existing exclusive R160 JSONL allowlist. Do not run tests or `run-mono-std`.

`dump-poly-std` records static source/lowering evidence only. It does not evaluate the samples or execute host writes. R149 runtime payloads remain unchanged and unobserved by this packet.

## Review checklist and stop rules

Independently verify source/API hash pins; exact one-file delta; unchanged module_map/finish/lock; exact sample/library hashes; fresh scratch paths and bounded write scope; output absence and exclusive creation; command consistency; 1200-second arithmetic; and the separation between compilation, valid static capture, accepted inference, and runtime behavior. Stop on any mismatch, existing output, offline failure, compiler error, observer failure, or exceeded bound. Preserve all partial evidence and leave every parent gate OPEN.
