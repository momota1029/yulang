# R184 owner-map result

Status: `NO_SAFE_CODE_CONTRACT`; read-only mapping complete against the exact
38 committed blobs in R184 revision 3, baseline `1ec02864dccccffa9617705b0ddbeaa64176aff5`.

Result note: `notes/design/2026-10-21-r183-option-b-owner-map.md`.

## Findings

- Existing if syntax and HIR support one body expression/block per arm; there
  is no branch expression-sequence form.
- Existing record-tail parsing is projection syntax. No general record literal
  CST/HIR/type/value/runtime form or field/spread consumer is established.
- Current candidate constraints explicitly handle if condition, branch value,
  and effects; no-else if produces Unit. New sequence/record forms would need
  source identity, graph traversal, solver/effect/scope consumers, runtime
  instruction/value and continuation integration.
- Runtime lowering and machine execution are experimental playground owners.
  The Web route is `main.ts` -> WASM `run` -> playground `execute`; the target
  ordinary-islands fixture is not currently in Web sample/smoke coverage.
- The unchanged fixture must eventually assert `countdown_result -> 8`; this
  map did not run it.

## Missing evidence / next step

No implementation contract can safely be prepared from these inputs alone.
Prepare a sequential manifest revision pinning the grammar/semantic decision
for record literals and spreads, exhaustive source-HIR and solver consumers,
runtime formatting/continuation/public route owners, and focused tests. The
design note lists the precise owner classes and required tests. Keep R183's
frontier-coverage proof and all parent/source-native/production gates open.

No compiler source, tests, build, probe, sample execution, or external Yulang2
worktree was touched. No code authority follows from this result.
