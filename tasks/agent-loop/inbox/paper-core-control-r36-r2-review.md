# R36/r2 independent source review

**CLEAN for the bounded R36/r2 repair.** No BLOCKING, major or minor conformance finding.

- `PaperCoreControl.lean:75–105` matches the supplied frozen r1-to-r2 diff: five named R35-supported heads extract mapped-success evidence; remaining unsupported heads contradict success. No new premise or helper appears. Authority: r2 contract `:23–35`; `PaperCoreStep.lean:129–142`.
- `PaperCoreControl.lean:11–43,108–177` preserves shared `d/g/e`, distinct intermediate and final types, innermost-first stack order, push priority, capture-avoiding pop and lifting through every stored let frame. Authority: parent contract **Fixed goal**; manuscript `:203–240,305–316,331–334,1014–1026`; `PaperTermSubstitution.lean:223–225,267–278,727–731`.
- All eight printed theorem types match the source. Recorded complete axiom sets are empty for `plug_typed` and `erase_typed`, and `[propext, Quot.sound]` for the other six. The complete log was scanned; command/audit blocks were inspected. Both recorded commands exit 0. These are recorded checker results, without independent build certification.
- Handoff `:78–102` accurately limits the result to finite ordinary let control and partial R35 steps. Full state/current-port/residual-graph correspondence, omitted frames, source/native, inference A/B and production remain OPEN. Authority: r2 contract `:37–41`; manuscript `:55–62,1860–1875`.
- No specification change or expected-output change is introduced. Tests, fixtures, diagnostics and semantic test names remain outside this packet; any future expectation change requires the authority review in `rules/testing.md`, **Expected-output protection**.

Confirmed the five supplied contract/source/log/handoff/primary-receipt SHA-256 values. Exact historical diff provenance comes from Luna’s supplied frozen diff; no Git operation was performed.

Reviewer `/root/r36_r2_independent_m1`; session/model/effort UNKNOWN. Review stopped at 2026-10-25 19:16:37 UTC, 83 seconds after intake. No files written, descendants started, or checker/cache/Git/network operations performed. Returned to Luna for persistence under the governing read-only restriction.
