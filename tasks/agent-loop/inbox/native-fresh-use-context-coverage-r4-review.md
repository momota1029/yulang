# r4 Independent Review

Verdict: **REJECT sprint acceptance; retain Rust instrumentation and Lean terms as provisional, unchecked research. Context coverage remains OPEN.** No reachable successful counterexample is established.

Authenticated frozen artifacts:

| Artifact | SHA-256 |
|---|---|
| r4 contract | `a7ed1ad46c45c9a69e4db807f874b709716a7265dbe9d00eaa88275c7fbda11c` |
| Amendment 01 | `d8f5695ff461270e52d6a27bf0f09593a48a65e5fa2f4c5f5c6b77043730d02f` |
| Rust source | `4540af4c5f0c1c2f69f26363195a5b8b8c735c2638235aa9fd7cc390754d221e` |
| Lean source | `442c41c863e33396ea0759acc2e438d41fa2cd09033c2af18d221a1357bd3ace` |
| Rust handoff | `6ae81be632c07d7935efe787f36581c953ed62fd5650289f83bcb9db02fb097e` |
| Proof handoff | `b2a821bd17bcfb792f5a90d95ffe8303f947970aac2f48d1a00846d5cdd2090d` |

These match `current.json`. The four inspected Context/extrusion/effect/shadow dependency pins, r3 Lean import, and five amendment context pins also match.

1. **BLOCKING — Required native execution and restoration bridges remain unconstructed.**

   Target: `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR4.lean:195`, `:281`, and `:322`.

   Authority: r4 contract, **Fixed outcome**, paragraphs 2–3; **Required evidence and falsifiers §4**, line 67. Parent authority: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md §1`; `notes/design/2026-10-24-birth-level-scc-intrusion.md §6`.

   `completed_native_control_domain` derives exact reachability membership from a completed handwritten `NativeRun`. No interpretation establishes that actual successful Rust execution produces that run. The readback monotonicity theorem assumes seed inclusion for one fixed expression table; actual restoration does not have a proved seed-inclusion connection. `selected_renamed_weight` requires the mapped target already to be selected, so it cannot establish selection of every prepared image. The source and handoff disclose these limitations accurately.

   Classification: incomplete proof obligation, not an approved specification change or an identified false theorem.

   Closure: supply the native successful-execution interpretation and the actual restoration-to-readback argument, or the contract’s exact reachable successful counterexample. Keep the current declarations conditional until then.

2. **major — Required authentic route specimens are missing from the added test contract.**

   Target: `isolated/native-fresh-use-context-coverage-r4/crates/yu-solver/src/candidate_scheme.rs:8523`; completion instrumentation at `:4405` and `:5362`; suspension marker at `:5273`.

   Authority: r4 contract, **Required evidence and falsifiers §§1,3**, lines 64 and 66; **r3 evidence and corrections**.

   The sole added test constructs observation sets manually. Its identity, empty, and Partial cases do not invoke module/local construction or restoration. Instrumentation now runs inside authentic consumer functions, but the artifact adds no explicit specimens establishing which module/local cases reach it with shared DAGs, weighted contexts, discharged parents, and restoration. `Partial` is assigned inside the script harness after receiving `LocalRun::Paused`; `LocalScriptObservation` does not expose that coverage disposition for an authentic pause assertion.

   Classification: verification/specimen gap. Source inspection alone does not establish a successful-path implementation failure.

   Closure: provide source-level specimens that explicitly exercise and assert these cases through the admitted module/local routes, including observable incomplete disposition at a real pre-bound pause. Execute them only under the review and resource conditions of a subsequently accepted packet.

3. **major — Mutation coverage does not satisfy the enumerated falsifiers.**

   Target: the same Rust file, `:664`, particularly `:677`, `:689`, and `:696`.

   Authority: r4 contract, **Required evidence and falsifiers §2**, line 65.

   The helper mutates only the first source root; it deletes and inserts map keys but has no replacement-key case. Its child mutation removes an arbitrary nonidentity member of `target_contexts`, which may be a root rather than a shared child. Weight mutations silently disappear when no target weight is present. The synthetic fixture contains no weights and does not establish an authentic shared-child case. Consequently, a passing helper would not demonstrate every promised mutation category.

   Classification: implementation gap in the research instrument’s falsifier coverage.

   Closure: demonstrate the specified mutations against unchanged authentic construction/readback evidence, with explicit witnesses ensuring shared-child and weight cases are exercised rather than skipped.

4. **minor — Reviewer ACK ordering deviated from the contract.**

   Target: this reviewer’s startup procedure.

   Authority: r4 contract, **Assignments and exact output paths**, line 60.

   I read governing material and the first Lean source segment before sending the required ACK. I disclosed this immediately; Luna instructed continuation with the deviation recorded. Producer source was inspected before handoff bodies.

   Classification: procedure deviation. This review must not be described as fully contract-compliant.

   Closure: retain the deviation in the review receipt; enforce ACK-before-body ordering for future packets.

The r3 local corrections show useful progress. Identity is excluded from stored-row requirements, completed-empty evidence is explicit, source roots and closures are captured before rename, and later admission roots are compared with preparation roots. Post-restoration closure traversal uses actual borrowed `CircuitEvidence`. Those observations support further investigation, subject to the findings above.

No existing expectation, golden, diagnostic, fixture, or semantic test name was changed in the inspected diff. No new semantic decision or user approval is supplied by this review.

All original source/native, A/B, inference-soundness, effect-hygiene, principality, termination, and production obligations remain OPEN; `H_u` remains AUTHORITY_BLOCKED. Nineteen Lean theorem terms remain unchecked, including their unchecked r3 dependency. I ran no tests, builds, Cargo, Lean/Lake, checker, or Git commands; made no writes; and spawned no descendants. Actual model/effort and exact elapsed resource usage are UNKNOWN. Review stopped within the 600-second grant by local estimate.
