# Sprint NATIVE-FRESH-USE-CONTEXT-COVERAGE/r4 — native completed-consumer bridge

Status: CANDIDATE until Luna records live admission and exact leases in `tasks/agent-loop/current.json`.
Branch / primary baseline: `yulang3` / `1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`.
Research base: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`; clean isolated workspace with only the three admitted Rust source overlays plus this sprint's leased work. No r3 candidate bytes are overlaid into the baseline.

## Fixed outcome

Establish an authentic Context coverage implementation and native proof bridge at completed FreshUse consumers, or produce an exact reachable successful restoration trace that defeats the coverage claim. This is a bounded observation/coverage gate. Full FreshUse validation, map-choice/payload correctness, returned-root theorem, source/native soundness, effect hygiene, `H_u`, principality, termination and production are excluded and remain separate OPEN gates.

Use the existing APIs and pinned scheme/Context/restoration owners. Derive actual source roots independently of the candidate map. Derive exact rename keys from successful Context traversal and match logical identity without pretending it is a stored row. At module and local completed consumers, authenticate the final map roots, child closure and weight observations against the same native construction and borrowed readback. Separate successful empty completion from pre-bound suspension; the latter must return explicit `Partial/Unavailable`, never ordinary success evidence.

Build a source-qualified execution-to-projection bridge: connect successful native rename transitions to the finite-DAG/domain theorem, account for opposite-bound restoration and discharge/residual changes, and show every prepared map image needed by the consumer remains observable after restoration. If this fails, the required counterexample must be an actually reachable successful native trace, not merely a local state update or abstract witness. No theorem hypothesis may restate domain equality, image observability, or restoration noninterference.

## r3 evidence and corrections

r3 is `CLOSED_INCOMPLETE` at `tasks/agent-loop/history/native-fresh-use-context-coverage-20261028-r3-outcome.md`. Its Rust source was REJECTED; its 16 Lean declarations are unchecked partial research. Preserve all r3 bytes and hashes. The independent review identified: (1) logical identity was inserted into a stored-readback set although `CircuitEvidence.contexts()` omits ID 0; (2) the empty positive fixture contradicts its false completion guard; (3) the predicate ignores independently supplied `source_roots` and synthetic mutations do not validate native maps; (4) suspension returns `Ok(())` without explicit `Partial/Unavailable`; (5) abstract proof projection is not connected to native execution or restoration. Fix these defects in r4's isolated artifact. Do not change language semantics, APIs, production code, expected outputs or named goldens.

## Exact inputs

The clean workspace starts from the pinned research base and overlays exactly these three baseline Rust files:

- `crates/yu-solver/src/candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- `crates/yu-solver/src/candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Admitted read dependencies, all exact hashes:

- `crates/yu-solver/src/candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/src/term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- `crates/yu-solver/src/candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- Lean `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- Lean `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- Lean `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` (Lean 4.35.0)
- Lean `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md`: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- governed `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- governed `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- admitted r3 source investigation, read-only only: `isolated/native-fresh-use-context-coverage-r3/crates/yu-solver/src/candidate_scheme.rs`, `9279fcb9bd1580655b7db4541c27338cc3a48ac711f06197cd3ee250b5315923`
- admitted r3 partial Lean research, read-only only: `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR3.lean`, `735c0711151c4605d40b338792327f30af80e9740cce346b65517df722543d46`
- r3 frozen review and outcome: `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r3-review.md`, `2bdb5816a94d62fe8cda53fcb84a0e98688c4ea21f53940dfa48a04e56d3b3b6`; `tasks/agent-loop/history/native-fresh-use-context-coverage-20261028-r3-outcome.md`, `b458d69a9dd9f2f34f93f6abd804f72e13ae22c08edc95f8b09239bbbde49157`.

No other owner or dependency is admitted. Any additional dependency requires a Luna-authored versioned amendment before body reads.

## Assignments and exact output paths

- Implementation, requested Luna/high, 800s: only `isolated/native-fresh-use-context-coverage-r4/crates/yu-solver/src/candidate_scheme.rs` and `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r4-rust.md`.
- Proof, requested Sol/high, 800s: only `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR4.lean` and `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r4-proof.md`.
- Fresh independent review, 600s after freeze: only `tasks/agent-loop/inbox/native-fresh-use-context-coverage-r4-review.md` (reviewer may return a read-only report by message if its role forbids writes; Luna then captures it without changing the verdict).
- Primary-only caches: `isolated/native-fresh-use-context-coverage-r4/target` and `notes/theory/lean/.task-tmp-native-fresh-use-context-coverage-r4`.

Every worker first ACKs this exact contract hash, requested/observed model and effort (UNKNOWN if not exposed), exact lease, remaining grant, and current session before source-body reads. No descendants or path expansion.

## Required evidence and falsifiers

1. Logical identity is represented semantically and never fabricated as a stored readback row. The empty completed consumer has explicit completed evidence; pre-bound suspension returns `Partial/Unavailable`. Exercise both through their actual routes.
2. The coverage predicate consumes independently obtained source roots and exact native map keys. Mutate each source-root input, map key (delete/insert/replace), target root, shared child and weight against unchanged authentic construction/readback evidence. Synthetic copied sets alone do not count.
3. Run actual module and local completed FreshUse routes, including identity, shared DAG, no-relation/empty bounds, discharged parents and restoration. Show post-bound child/weight observations from real `CircuitEvidence` readback. Do not claim broad success if an admitted constructor is missing.
4. Prove execution-to-projection correspondence for native rename traversal and exact domain, then establish sufficient target and weight observation across the actual restoration driver. A local discharge mutation is not a counterexample unless an admitted successful trace reaches it. Conversely, no stability hypothesis may merely state the needed image coverage.
5. If a reachable successful trace defeats coverage, freeze the shortest exact constructor/state/restore/admission/readback sequence and identify the first omitted image. Do not expand semantics or production/API scope.
6. Fresh review must inspect source before handoffs, verify exact hashes, all above cases, theorem hypotheses and limitations. It may not run checks. After acceptance only, primary may run the contract-authorized focused Rust checks and pinned Lean 4.35 verification plus complete theorem axiom audits. A review rejection closes the sprint incomplete without running checks.

The original parent, effect-hygiene, source/native, principality, termination, production and `H_u` gates remain unchanged and OPEN/AUTHORITY_BLOCKED. No partial result promotes them.

## Resources

Fresh 2,600s total; no r3 carryover: implementation 800s, proof 800s, reviewer 600s, primary verification/integration 300s, contingency 100s (not producer authority). Zero Astra. At most two Cargo attempts, aggregate 180s and 2 GiB RSS, one CPU; at most two Lean attempts, aggregate 240s with `-j1 -M1024`; one heavy process at a time. Freeze both lanes before review. Stop at exact caps.

Capacity plan: primary + existing UNKNOWN `/root/effect_permission_module_environment_source` reservation + two producers + one reviewer + primary integration reservation = 6. Preserve every UNKNOWN state/quarantine. No capacity override is requested. Selector recommendation is not itself admission.

At sprint end, record hashes, outcome, spent budgets, review and gate disposition in current/history. Stage no unrelated paths. Luna alone integrates an explicitly reviewed coherent checkpoint after full outbound-range inspection; no force-push.
