# R91 Lean input flatten correction

This primary-owned record corrects the flattening recipe after the first authorized direct Lean invocation failed before checking any declaration.

## Call 1 disposition

The 934,982-byte input authorized in `r91-lean-call-authorization-01.md` had SHA-256 `d0b42e35ea434d79f41d56a7788c30a9cd3d71bbd5cecc0111b32903b10044c4`. It exited 1 after 14.786 seconds. Stdout was 94 bytes, SHA-256 `1a798c59f7297904df59d1b1e97f3e26af936fcf8dc996dc0a477b06a6e51d78`, containing only:

```text
<stdin>:2375:0: error: invalid 'import' command, it must be used in the beginning of the file
```

Stderr was empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). No theorem was checked and no type or axiom result was produced. The executable was `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Invocation settings were `-j1 -M1024 --stdin`, `LEAN_NUM_THREADS=1`, 120-second timeout; observed exit and elapsed time are above. The pinned toolchain path identifies Lean 4.35.0; `--version` was not separately invoked.

The failure came from the handoff recipe retaining `import Init` in `NativeClosureEnvironment.lean`, `Contracts.lean`, and `NativeDictionaryDenotation.lean`. Any import command in a flattened body after the first line is invalid. This was not a candidate theorem failure.

## Corrected in-memory input proposed for call 2

Keep the same 22-file order and preserve every non-import source byte and line ending. Across the 22 files, retain the initial `import Std` line from `OriginalSourceSyntax.lean` as the first line. Remove every other line beginning exactly `import `, including all `import YulangClosure.*` lines and the redundant `import Init` lines. Join the complete retained bodies with one LF byte. No source module or candidate is edited by this transformation.

- Corrected stdin: 934,946 bytes.
- SHA-256: `54333b38794858ce2dccd2c8a44f1aa1a1c4ee8832964e3307c791c223a8ae44`.
- Source files: 22/22 end in LF; the only remaining import is `import Std` on line 1.

This correction still requires an independent pre-execution review and a pushed exact authorization before execution. No second call is authorized by this record alone.
