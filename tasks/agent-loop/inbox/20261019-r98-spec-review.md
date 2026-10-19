# R98 independent pre-edit specification review

Reviewer: fresh `spec_auditor`, independent/read-only; primary-preserved report.

**CLEAN — pre-edit plan only. No blocking or major specification conflict found.**

Verified SHA-256:

- Contract: `e5fb81b1ff423726fa853dcaf5c99deba4f3b286d1d84111268143872e95d4dd`
- `runtime_resume.rs`: `3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd`
- `continuation.rs`: `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`
- `machine.rs`: `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`

The fixture is type-plausible: `tick` receives integer responses; its saved suffix passes that integer to bool-returning `other`. Both receiving functions produce bool. The first result `true` reaches the second application of the same lexically bound `k`; its handler predicts `false`. Replacing only the specified operation pattern predicts outward `other` with payload `11` or `23`, respectively. These remain hypotheses.

Review caveats:

- **minor — pending evidence:** contract lines 22–25 specify the two single-pattern changes; actual variants do not yet exist. Authority: contract §Frozen positive fixture; `rules/testing.md` §Expected-output protection. **Closure:** inspect the frozen test and verify each variant changes exactly its specified pattern.
- **minor — pending correspondence:** contract line 31 requires authentic constructors, current receiving observations and exact selection/forwarding. Authority: parent capture-projection note §§1–3, 7; typed-source-owner realization §§1–3; ordinary-computation semantics §§2, 5. **Closure:** independently review the fixture-specific proof. R88’s exact U/O/S bridge supplies no whole-source authority for this fixture.

No old expectations are changed in the reviewed baseline. Keep existing tests, helpers and semantic names intact. An unexpected result stops R98; changing expectations to accommodate it requires the authority assessment and pre-write review mandated by `rules/testing.md`.

No general continuation safety, handler restoration, native projection or parent closure follows. No writes, tests, builds, runtime commands or Git operations performed.

## Post-freeze spec delta confirmation

Reviewer: same independent `spec_auditor`, read-only; primary-preserved report.

**CLEAN — frozen specification delta. Both pre-edit minor caveats are closed within bounded scope.**

- `runtime_resume.rs:434–487`: decoded positive source matches the contract. Each negative changes exactly one intended operation-name token (`other` → `tick`) in its designated Catch pattern. Each replacement needle occurs once.
- Removing precisely the added test reconstructs SHA-256 `3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd`. Existing tests and helpers are byte unchanged.
- Proof §§2–5 binds actual source bytes, formal/name/operation identities and the finite `Hole/Bind/View/Owner` chain. Its explanation that `ForwardHandler` is absent from the original capture is consistent with selection stopping capture; unmatched negative handlers enter suspended forwarding suffixes without subsequent template capture.
- Proof §§1, 3, 5–6 preserves the distinction between constructor reasoning and unobserved execution. It asserts no general Resume theorem, source-language handler restoration, whole-source typing, native projection or parent closure. R88 is explicitly bounded.

Authority: R98 contract §§Frozen positive fixture, Proof obligation, Leases and verification; `rules/testing.md` §Expected-output protection; capture-projection note §§1–3, 7; typed-source-owner realization §§1–3; ordinary-computation semantics §§2, 5.

Verified frozen hashes:

| Artifact | SHA-256 |
|---|---|
| Test | `449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580` |
| Proof | `923a01e7078d3861a819b4eeab67a61543f5db04ebdca5ae1be1a68294093975` |
| Proof handoff | `4e73b3c4c4c71c7217abdc52b0765a2a68c6f9c0bcd0cc74e3140042749b74eb` |
| Implementation handoff | `7bdce2ee736281be6da118b011d932c7334ca566b57c77710bd3098a8952f0c2` |

No new findings. Preparation and all three outcomes remain unobserved. Fresh compiler/source review and the contract’s single authorized execution remain required. No files written; no tests, builds, runtime CLI or Git operations run.
