# R165 candidate handoff — native admission and checked-out evaluator

- Fixed goal: implement natural Simple-sub inference/evaluator behavior with proof; broaden unchanged Yulang2 Web sample execution. Scope and A/B quantifiers remain unchanged.
- Candidate contract: `tasks/agent-loop/sprints/native-admission-and-module-schedule-20261020-r165.md`; freeze its exact SHA-256 after review/repair.
- Checkout baseline: `research/simple-sub-intrusion`, HEAD `09f5108098d55bc09326ace1f05ca6b6aaf667e1`.
- Proof outcome: original forwarding-preservation §6 mapped-bound admission by constructor-to-consumer argument, or exact first missing premise/counterexample; R70/R71 consumed only conditionally.
- Proof outputs: `notes/theory/2026-10-20-native-forwarding-admission.md` and `tasks/agent-loop/inbox/20261020-native-forwarding-admission.md`; solver files read-only.
- Implementation outcome: conditionally correct the checked-out `RuntimeProgram::from_hir` source-schedule classifier for `Instruction::Case`, only after independent review confirms the established “may be a computation initializer” rule and early evaluation of a pure case preserves semantics.
- Only production write path: `tools/inference-playground/src/runtime/program.rs`. No module-mode API or unsupported Y2 run.
- Check: one `cargo check -p yu-playground`; no tests, sample execution, Web edits or temp Y2 activity.
- Review: prospective source/contract review before grant; fresh final proof and exact code/check review before closeout.
- Budget: 2,040s total, Astra 0, no carryover: prep 240 + prospective review 120 + proof 600 + implementation 720 + final review 240 + closeout 120.
- All R149 imports, tuples, primitives, roles, host writes, publication, complete module schedule and expected outputs remain OPEN; original A/B, inference/evaluator and production gates remain OPEN.
- Status: candidate only; no lane or command authorized yet.
