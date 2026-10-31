# R83 audit 1 result — dependency prefix rejected

Authorization was committed and pushed as `eef99bdd9` before execution. Exact input was reconstructed in memory from the reviewed 220 declaration slices and 215 prefix queries.

- Input: 92,456 bytes, SHA-256 `c42cc473b7a1629cedb796b30dae79bfcc41a597e5ca8e5afce4136183bd4146`.
- Pinned Lean executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Command `lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 s.
- Exit 1; elapsed 9.072 s; no timeout. Stdout 99,014 bytes, SHA-256 `ea872eb250a2be838d0ab788375ab2a5eda66c9214d8a6947aa8a58d26b1de9b`; stderr 0 bytes, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- First diagnostic: ambiguous unqualified `unique`, visible from both `SourceInternalContextR55` and `ProviderNativeContextR57`; later `invalidField`, unsolved goals, fixture tactic failures and `Unknown option pp.width` also occur. Full stdin/stdout/stderr bytes are preserved in the R83 proof handoff audit receipt.

No R83 theorem-type/axiom report was queried or accepted. Audit 2 was not run. This result identifies an assembly namespace ambiguity and invalid pretty-print option; later errors remain unclassified until a repaired prefix is checked.
