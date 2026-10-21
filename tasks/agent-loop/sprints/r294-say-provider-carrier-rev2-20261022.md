# Sprint R294 — retain the pinned `say` provider carrier (rev2)

Status: solo implementation/source-correspondence checkpoint; parent R149 stays open.
Supersedes: `r294-say-provider-carrier-20261022.md` after a concrete lowering-path probe.

## Parent and goal

Continue unchanged Yulang2 Types/Console under `notes/design/2026-10-20-r149-types-console.md`. R293 resolved pinned public `say` to `std::io::console`, but the HIR built with `lower_module_with_source_identity` has no owner because ordinary `plain_binding_header` does not admit the pinned parenthesized formal syntax.

A direct full-module `lower_module_with_local_source` probe is not a viable provider entrypoint: pinned `console.yu` fails with `StructuralProjection` on declaration forms including `pub host act out`; isolated `say`, `print`, `println`, `note`, `eprint`, `eprintln`, and `dd` lower through this path. The normal `lower_module` entrypoint already enables `ordinary_source_carriers` and is the target.

Extend the existing ordinary source-carrier header admission to retain a single parenthesized typed formal such as `say(value: 'a)`. Build the exact pinned console provider through `lower_module`, join `say` to its source export, and verify that its own ordinary source carrier retains `where 'a: Display` with same-parse source identity. Keep other existing parsing/error behavior intact.

## Boundary

This admits the source-owned binding and carrier only. It does not consume the `where` premise, resolve `Display`, construct an imported scheme, implement multi-HIR inference, or claim either sample runs. The `[io]` contravariant open-row interpretation `[io,'e]` remains unchanged.

No spelling intrinsic, chosen method, changed source bytes, or new restriction. Public export route resolution remains authoritative. Recovered and unsupported syntax stays fail-closed.

## Exact paths

- `crates/yu-hir/src/module.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this rev2 contract
- `notes/theory/2026-10-22-r294-say-provider-carrier.md`

No other paths are leased. No subagents are used under the user's explicit solo-work instruction; dispatch is degraded solo.

## Evidence and stop point

Use the exact 40-module pinned closure and the same `ParsedFile` for index and provider HIR. Verify the old source-identity-only artifact still lacks `say`; verify normal `lower_module` now retains its exact public binding and supported source carrier; verify the carrier has one declaration-owned `where` clause, subject `'a`, role `Display`, and a key owned by that parse. Also keep exact `println` and `Display` ownership checks.

Run the focused pinned-owner test, `cargo check -p yu-hir`, `cargo check -p yu-playground`, `git diff --check`, and agent-sprint static checks. This is source-carrier evidence only. Imported typing, role evidence, runtime behavior, theorem closure, and production remain OPEN.
