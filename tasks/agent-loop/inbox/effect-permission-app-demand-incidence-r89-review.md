# R89 proof pre-execution review and audit authorization

Sprint: `EFFECT-PERMISSION-APP-DEMAND-INCIDENCE/20261101-R89`.

## Independent pre-execution review

Reviewer: `/root/r86_independent_review`, independent read-only reviewer, neither proof author nor primary.

Verdict: **PASS for pre-execution readiness; Lean acceptance remains pending.** The reviewer matched the candidate (`notes/theory/lean/YulangClosure/SourceAppDemandIncidenceR89.lean`, 8,967 bytes, SHA-256 `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`) and proof handoff (`tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-proof.md`, 11,169 bytes, SHA-256 `a529fa1ae1d3dc25f6b986499a5fe93a55ea3122e46ff0a5262ce2bb8b8cc49a`). All four statement texts remain byte-identical to R88. The explicit `AtomKind.roleAndInitialCallOrigin` fixes the reported ambiguity; `app_rule` rewrites the actual `sourceRules` equation before reduction. All original premises, both children, annotations and one shared witness remain. No proof hole or kernel bypass was found.

The reviewer independently matched both the original R89 manifest (33/33 inputs) and amended manifest r2 (34/34 inputs). Scope remains structural App inversion over the parameterized Kernel; native incidence, qualified extrusion, joint lift and A/B remain open. The reviewer ran no Lean, build or tests.

## Primary exact-input authorization — call 1 of at most 2

Authorized by the R89 contract and the fresh PASS above. This records the exact stdin and executable preflight before the primary's first direct invocation.

Flattening recipe, in memory, dependency-first: read the pinned `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, then the frozen R89 candidate as exact bytes; remove only lines beginning with `import YulangClosure.` from the latter two; retain `import Std`; concatenate without writing an intermediate file. The candidate already contains all three helper `#print`s and four complete `#check @...` / `#print axioms ...` pairs.

- `OriginalSourceSyntax.lean`: 22,040 bytes, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `OriginalSourceGeneration.lean`: 66,485 bytes, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- R89 candidate: 8,967 bytes, SHA-256 `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`.
- Exact flattened stdin: 97,404 bytes, SHA-256 `e72174bdab2961be92b3577f2bf7ecf4b88af3ac6edce154a4f74868b023f199`.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; version Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Invocation: `lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 seconds.
- No Lake, build, test, cache, scratch, output file, worktree or environment is authorized or created.

This authorization covers only call 1 and these exact bytes. Exit, stdout/stderr, printed theorem types, and complete axiom results are pending execution and will be appended as a new receipt.
