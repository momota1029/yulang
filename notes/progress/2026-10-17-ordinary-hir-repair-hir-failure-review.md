# Post-run review: recovery refusal assertion

Fresh read-only reviewer `/root/ordinary_hir_repair_hir_failure_review`
(`regression_auditor`; requested gpt-6.1-sol/low; observed model/effort
UNKNOWN) STOPPED with one MAJOR test-contract inconsistency. Exact elapsed
unavailable; full90s cap charged conservatively. No edits, tests, builds, Cargo,
probes, formatting, Git, network or descendants.

Finding: the test at
`crates/yu-hir/tests/ordinary_application_admission.rs:326` expects a module-wide
`UnsupportedExpression` for `my prior = @; my broken = f(`. The existing ordinary
recovery path at `crates/yu-hir/src/module.rs:2196–2204` checks `has_recovery`
before structural projection/unsupported fallback and returns
`ResolvedExpr::Error` with causal IDs. It does not add `UnsupportedExpression`.
This behavior matches adopted successor §3 (preserve existing recovery form and
diagnostics) and §4 (recovery gate/order and causal attachment). Adding an
unsupported diagnostic to pass the assertion would require a new semantic
choice; no such choice is authorized. The compiled failure is not formatting
noise and is not a demonstrated source-implementation defect.

The pinned run reached line326 after lines322–325 passed: no Apply, a retained
causal Error with nonempty IDs, and no unresolved-name diagnostic. The
inherited-error-kind assertion at line327 did not execute and remains unverified.
The broader §2 wording needs narrow adjudication against §§3–4 and the actual
fixture. Minimum test repair, only if a fresh spec audit confirms the scoped
reading: check the `broken` binding's exact causal IDs/attachments and inherited
kind, and verify no hidden operand resolution; do not merely delete line326 or
weaken refusal assertions. Do not change source semantics.

Pins verified: rev6 contract
`3d3f8fd3643bf3b1d27793f470f19b430779bc24f1698788d89295e770c258a4`, adopted
rev4 `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`, lib.rs
`cf0a2d537df793986509175fbde2785731ac28f4bc3f2024f4f0fbca2127c5ed`, module.rs
`60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed`, and HIR
test `dd6c2ac5f5e8b50e37637a84e3f7427a1f628cd0f8edcaa2803775ab702ba972`.
Focused unit tests passed8/8, including all three named falsifiers. HIR
integration passed8/9. Solver integration did not run. Original theorem
conditions closed: 0; all parent gates OPEN.
