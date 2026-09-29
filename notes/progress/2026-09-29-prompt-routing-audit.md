# Prompt-routing audit — 2026-09-29

Scope: user-requested audit/fix of Luna-led, bounded Sol orchestration on
`yulang3`, starting at `fa93391684622b3c4fbaf7fa8f0a6ccba0dde1e2`.
This is repository-policy alignment, not a compiler implementation gate or a
new Authoritative language/design decision.

Aligned the active role matrix and architect/performance triggers with the
existing M0–M3 budget; removed stale Terra/unpinned-role assumptions without
changing `.codex` model/effort settings. Made primary-owned child dispatch and
bounded evidence packets explicit. Scoped the old migration-only compiler-edit
restriction to actual policy/configuration maintenance. Preserved frozen main,
test-expectation authority, human design decisions, review independence,
frequent coherent pushes, and the conversation/artifact boundary.

Verification: original AGENTS blob hash checked before amendment; focused
source/contract assertions checked branch protection, role routing, budget
limits, expected-output review, primary-only delegation, and byte-identical
communication/verification sections. No compiler test, benchmark, live Codex
model execution, or independent subagent review ran in this connector session.
These checks are not a model-quality or token-cost evaluation.

No compiler source, tests, benchmarks, approved designs, or model pins changed.
`tasks/current.md` and the design index are intentionally not rewritten: this
maintenance pass does not change the active compiler gate/status, and must not
replace concurrent implementation progress with an audit checkpoint. This file
records the separate maintenance result; no compiler gate is marked complete.
