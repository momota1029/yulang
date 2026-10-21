# R286 — Assign source-qualified HIR identity to role declarations

Status: active solo continuation; dispatcher lane omitted under the user's explicit no-subagent constraint.
Baseline: `39947337d`. Parent: unchanged R149 Types/Console sample and proof goal.

## Outcome

Add an HIR sidecar for admitted source role declarations. The role identity is `(ModuleId, parse-owned RoleDeclaration SourceNodeKey)`, never a spelling-derived key. Retain the exact role head and optional body source owners/ranges/text so method and implementation identity can build on the same declaration. Keep HIR's current error item for the unimplemented semantic role path; this packet does not claim role lookup, selection, member checking, or code execution.

## Success and falsifiers

A role declaration in an otherwise lowered module has an unambiguous module/source identity and exact head/body correspondence. Two same-spelling declarations remain distinct IDs. Malformed recovery and unsupported declaration shapes fail closed. No source role meaning is inferred from spelling alone.

## Exact paths

`crates/yu-hir/src/module.rs`; `crates/yu-hir/src/module/source_role.rs`; `crates/yu-hir/src/shadow.rs`; focused HIR tests; this contract; `notes/theory/2026-10-22-r286-hir-role-declaration-identity.md`; `tasks/agent-loop/current.json`.

## Verification and limits

Focused HIR test, solver `--no-run`, sprint check, tooling unittest, diff check. Solo-authored, no independent review. Role imports, member IDs/signatures, implementation IDs, constraint generation/propagation, runtime method selection, sample outputs and all proof/production gates remain open.
