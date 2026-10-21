# R280 primary handoff — qualified constructor Pattern application

Contract: `tasks/agent-loop/sprints/r280-y2-qualified-constructor-pattern-application-20261022.md`.
Baseline: `d6c2c4914`. User constraint: solo primary, no delegated workers.

The rebuilt CLI reproduces the exact 15 paired `Missing/CaseArm` and `ErrorGroup/OperatorChain` frontiers at same-line payloads after `::`-qualified constructor paths. Existing Pattern ML application is admitted through GML classification, and plain `f x` already constructs an application node. The pinned qualified path plus same-line payload still fails at the arrow frontier. The parser now allows the arm-owned Pattern item after a completed qualified constructor path and retains the arrow boundary. Focused tests cover qualified payload forms, unqualified f x, GML application, and the case-arm arrow. The exact pinned fmt census is 2: root ErrorGroup at 5801..5813 and StringEscape Missing at 5800..5800; all 15 paired case diagnostics are gone.

The focused Pattern test, 80 Pattern tests, 34 case-like tests, exact fmt census, playground check, static check and diff check pass. R149 source/HIR correspondence, tuple traversal, role resolution, sample inference/output, source/native proof and production remain OPEN. The converted unified design and proof companion remain governing; the `[io]` open-row correction `[io,'e]` is preserved.
