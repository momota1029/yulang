# R278 primary handoff — Yulang2 dotted Pattern target

Contract: `tasks/agent-loop/sprints/r278-y2-dotted-pattern-target-20261021.md`.
Design addendum: `notes/design/2026-10-21-r278-y2-dotted-binding-pattern.md`.
Baseline: `0527c44ad`.
Status: CHECKPOINTED_UNREVIEWED; primary-only, no delegated workers.
Parent: unchanged R149 Types/Console and broader Yulang2 sample goal.

The pinned `fmt.yu` expresses required signatures and implementation members
with dotted Binding targets. R277 showed these among the parser's root recovery
groups. This sprint adds the parser-only Y3-native `PatternFieldTail` for an
identifier followed by adjacent `.identifier`. It preserves expression
FieldTail and `::` Pattern paths as distinct constructors. The exact pinned fmt
census fell from 50 diagnostics to 36: 21 root `ErrorGroup`, 7
`OperatorChain` `ErrorGroup`, and 7 missing `CaseArm` diagnostics.

No role resolution, HIR admission, type/effect result, execution, proof closure
or production promotion is claimed. The exact Y2 sample and pinned library
bytes remain unchanged. Preserve contravariant `[io]` as `[io,'e]`.

Checks: focused syntax tests and exact pinned-source diagnostic census pass;
`cargo check -p yu-playground` passes. Sprint static check and `git diff
--check` are run at close. No broad suite or independent review under
user-directed solo work. Parser, HIR, role lookup, sample output, source/native
proof and production remain OPEN.
