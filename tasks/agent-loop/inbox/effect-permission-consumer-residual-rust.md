# Rust handoff — EFFECT-PERMISSION-CONSUMER-RESIDUAL-20261028/r1

Handoff revision: 1  
Contract SHA-256: `a2d8b9a7aef7a142559370d9f5bd10d8fe0ee6d68f9bb4938d4167a11a86da7e`  
Assignment: isolate and classify the returned-computation consumer assertion  
Role requested: `implementer`, Luna/high  
Role/model observed: UNKNOWN (runtime metadata unavailable)  
Worker state: STOPPED after invocation 1; no second invocation or further Cargo work

## Lease and frozen artifacts

Writable repository paths were limited to:

- `crates/yu-solver/src/candidate_effect.rs` — current SHA-256 `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`.
- `crates/yu-solver/src/candidate_scheme.rs` — unchanged by this worker; SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
- This inbox file — handoff revision 1.

The test-only delta in `candidate_effect.rs` adds `formal_permission_consumer_residual_observation`, which runs the original unequal fixture and original consumer assertion with the unresolved `r != q` assertion disabled for this test invocation. The old unequal test still retains and executes its `r != q` assertion. The helper now separates source-fixture selection, unequal-transport assertion and consumer assertion flags. A `cfg(test)` census prints the returned answer graph's effect-operand forms keyed against the fixture's resolved `state` effect ID. The original consumer predicate and its message are unchanged. No production signature or call path, expected output, diagnostic or source fixture text changed. `candidate_scheme.rs` was not edited.

## Outcome and exact source-semantic finding

Outcome class: **provisional source-native evidence**, adjudicated as a **fixture expectation defect** (admissible outcome 2). This does not establish a solver propagation defect or a source-qualified counterexample.

The fixture text is embedded at `candidate_effect.rs:3225` and `:3230`:

```yu
my f(pair:((int -> [io] ()), (int, int -> [io] ()))) = f pair
my callback n = state::tick n
my answer ignored = case f (callback,(0,callback)):
    (left,_) -> left 0
```

`callback` is stateful and `answer` calls `left 0`, but the source does not connect `left` to the callback supplied in `pair`. The body of `f` is a recursive call to `f` with `pair`; it contains no return of `pair`, projection from `pair`, or other provider construction. The `left` binding comes from the recursive call's result. The authoritative local self-recursive rule says a recursive occurrence uses the same open monomorphic root; it does not identify a recursive call's result with its argument/provider: `notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source behavior” and “Proposed source-to-solver seam”, SHA-256 `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895`. Thus `left 0` is a demand on the *result type* of `f`, but the source supplies no return-provider path from the stateful input callback to that result. Operational return/reachability is also not established; the body is self-recursive and the termination gate is open.

The selected annotation semantics distinguish Permission, actual inflow and residual, and say the actual handler performs subtraction: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1.2, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`. The adopted negative-port definition likewise says Permission alone creates no contribution/subtraction and requires an actual source-derived consumer: `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md` §§2–3, SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`, adopted by `notes/design/2026-10-17-source-formation-proposals-adoption.md`, SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`. This fixture contains no Catch/handler. `CandidateGraphExport::formal_effect_permissions` at `shadow_apply.rs:2680–2715` only exports source Permission paths onto captured effect ports. No subtraction transition exists in this fixture to observe.

The source-to-candidate trace reaches the `FormalAnnotation` constructor for `f`, retains its nested source paths and `[io]` permission metadata, captures those ports and returns the owner graph. The later source `answer` graph contains no `CandidateGraphEffectOperand` nodes in the focused observation. There is therefore no source-attributed `state` contribution joined through `f`'s returned result to validate. The missing evidence is the source return/provider link from `pair` to the result consumed as `left`; the missing subtraction evidence is a real handler and its actual selected contribution. Neither may be inferred from `callback`'s body alone.

## Invocation 1 — isolated failure and raw receipts

Luna explicitly released this exact invocation after independently verifying the frozen inputs. Invocation 1 ran only the isolated consumer test. It reached the original assertion without running the `r != q` assertion:

- Command: `/home/momota1029/.cargo/bin/cargo test --offline --locked --manifest-path crates/yu-solver/Cargo.toml --features shadow-apply-candidate --lib candidate_effect::tests::formal_permission_consumer_residual_observation -- --exact --test-threads=1`
- Frozen argv JSON: `/tmp/yulang-effect-permission-consumer-residual-20261028-r1/rust-target/argv.json`, SHA-256 `dc6226de053d1987403ced78894d0c3bdb0c5f2ef942259246d1b0422ef10197`.
- Frozen launcher: `/tmp/yulang-effect-permission-consumer-residual-20261028-r1/rust-target/run.sh`, SHA-256 `3bbc32d269f0483af5753c6c5f9706b623a886d521e8a830257fca5fcbb605bc`.
- Complete 280-entry input inventory: `/tmp/yulang-effect-permission-consumer-residual-20261028-r1/rust-target/input-inventory.json`, SHA-256 `a1785f08ca2fc0a2fbdae0e1dd1d1345e41c8d2db36180bc912f163def7560f0`; zero missing entries or hash/size mismatches at freeze and primary verification.
- Raw stdout SHA-256 `909397e3e687dc3a81ddc31c6d390e8f2097507b5620c58f38a097859dd21f46`; raw stderr SHA-256 `fcc2dda80f9ad3b6476a40854013d14b24edea4e6db275e958057480130ee54b`; status SHA-256 `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`; time SHA-256 `463dbc0d3112b2c98909a7b55ab16cee5bcb42890f25707176d92af395a9527b`.
- Result: exit 101 at `candidate_effect.rs:3428`, `state remains in the returned computation`; preceding census printed `consumer-returned-effect-forms=[]`. Wall 59.64 s; peak RSS 1,671,032 KiB; 0 swaps; CPU affinity 0, one Cargo job/thread, offline/locked, within the 120 s attempt cap. Preflight found 21,935,861,760 bytes available memory and no active Cargo/rustc/Lake/Lean process. RSS was measured by `/usr/bin/time -v`, not claimed OS-enforced.

No second invocation is authorized or performed. The isolated failure is preserved as evidence of the bad fixture expectation; the original failure/result is not made green by changing its expected output.

## Prior evidence reused or rejected

- Reused only as source navigation: the prior authenticated site-export outcome/review and accepted invocation-2 identity/delegation evidence. That evidence is not consumer-residual evidence and used a different identity fixture.
- Rejected for this consumer conclusion: prior invocation 1's result as standalone evidence, because its 271-entry input inventory is missing; the prior invocation-2 272-entry inventory cannot replace it. The current isolated run has its own complete, rehashed 280-entry inventory.
- The audited conditional Lean result remains conditional and supplies no source return/provider link, no subtraction transition and no whole-language/native closure. No Lean claim is used here.

## Checks, limitations and next related step

- `bash -n` on the frozen launcher — passed.
- `git diff --check -- crates/yu-solver/src/candidate_effect.rs` — passed.
- Focused Cargo test — reached the original consumer assertion and failed as recorded above; this is not a solver regression finding because the fixture premise is absent.
- Changed dependency recheck: contract, `candidate_scheme.rs`, `shadow_apply.rs`, `candidate_intrusion.rs`, `candidate_extrusion.rs`, solver `Cargo.toml` and `lib.rs` retained their contract-pinned hashes. Governing source documents and current `candidate_effect.rs` hashes are recorded above.

The test-only census is useful only as provisional evidence for a future source fixture whose returned provider is demonstrably connected to the input callback. Its falsifier is a reviewed source path that makes `f` return/project `pair` or otherwise joins the input callback to the value bound to `left`; the current fixture does not. Cleanup owner: Luna after independent review or when replacing the fixture under a separately approved source scope. Do not broaden the predicate, change the fixture, or treat this as effect subtraction.

Exact in-envelope next step: request the missing source-owner evidence for a returned-provider connection and a real handler/subtraction consumer, then rerun only under a newly frozen inventory and a fresh Luna release. No production fix, expected-output edit, semantic change or parent-gate promotion follows now.

## Paths, resources and stopped-writes receipt

Repository write path this packet adds: `tasks/agent-loop/inbox/effect-permission-consumer-residual-rust.md`. Modified leased source path: `crates/yu-solver/src/candidate_effect.rs`. `candidate_scheme.rs` was not modified by this worker. No Git operation or other repository path write occurred.

All generated/scratch paths are under `/tmp/yulang-effect-permission-consumer-residual-20261028-r1/rust-target/`: `input-inventory.json`, `argv.json`, `run.sh`, `build/`, `stdout.txt`, `stderr.txt`, `status.txt`, and `time.txt`. These are disposable primary-only hygiene targets; none were removed. No other new paths are known.

Writes and Cargo work stopped after invocation 1 and this frozen handoff. No descendants were launched. Worker state: STOPPED for this packet; no unresolved descendant lease. No commit-ready milestone or independent review is claimed.
