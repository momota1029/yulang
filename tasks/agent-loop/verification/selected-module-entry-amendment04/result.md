# Verification result — amendment 04

Disposition: **two focused regression tests PASS** for the admitted research baseline. This does not close a proof or production gate.

## Exact execution

Frozen plan SHA-256: `ac59aacdb15b6aaa9c9c81b1b6bffc07bfe23e669cf2c93404ae4c9d1a6ac749`.
Preflight SHA-256: `d81b351c86cd9d06afa9790f5bc0a4f938784f40794d0780f02402ddf97dd3c9`.

The frozen command used a single systemd scope with `MemoryMax=2G`, `MemorySwapMax=0`, `CPUQuota=100%`, `taskset -c 0`, `CARGO_BUILD_JOBS=1`, `CARGO_NET_OFFLINE=true`, `--locked`, the amendment-specific Cargo target directory and `TMPDIR`, and an aggregate 180-second timeout. Both test invocations ran in order; the second was guarded by `&&` and could run only after the first passed.

1. `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership` — **PASS**, 1 passed, 822 filtered out.
2. `candidate_effect::tests::formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity` — **PASS**, 1 passed, 822 filtered out.

Cargo built the `yu-solver` library tests with `shadow-apply-candidate`; compilation emitted 22 existing dead-code/unused warnings. Total elapsed wall time: 63.48 seconds. GNU time reported maximum RSS 1,670,876 KiB (below 2 GiB), 95% CPU, zero swaps, exit status 0. Preflight recorded 20,551,456 kB available memory, CPU 0 available, and no active Cargo or rustc process. The transient scope resource-limit preflight succeeded.

## Frozen output hashes

| Output | SHA-256 |
|---|---|
| `run-01-original-regression.log` | `8e826331623dd12fca839905f854a232e846920bc8e53bae324baa56d3cb5e22` |
| `run-02-missing-constructor-trace.log` | `592072ac46780c228b75c99c7ebfbb2dfde83ae0b5fc7c957e1a2179f5fd1fc1` |
| `resource-and-supervisor.log` | `798bca1994be2ef78fd868a04dd1b9f58ebf32d034493f2946b4615120dca255` |

The three isolated owner hashes were rechecked after execution and unchanged:

- `candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Not run: recursive transport probe, broader `formal_permission` filter, workspace suite, Lean, and any production-path check. The unresolved unequal-transport assertion remains unverified. Native reconstruction and whole-branch allocation-root correspondence, H_u, A/B, effect-hygiene, and production gates remain OPEN or AUTHORITY_BLOCKED. No source bytes changed during verification.
