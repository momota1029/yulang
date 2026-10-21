# Sprint R294 — retain the pinned `say` provider carrier

Status: superseded initial contract; rev2 is the active R294 contract.

## Parent and goal

Continue the unchanged Yulang2 Types/Console goal under `notes/design/2026-10-20-r149-types-console.md` and the original R149 contracts. The exact pinned `std::io::console::say` declaration is a necessary imported value on the Console path. R293 found its public source export but no owner in the provider HIR built by `lower_module_with_source_identity`.

Establish whether the existing LocalSource-aware provider path admits the exact binding and retains its declaration-local `where 'a: Display` carrier. If it does, connect the provider HIR owner and carrier in the pinned-source test without synthesizing a value or role judgment. If it does not, identify the exact unsupported constructor and fix only the owner-local carrier path needed for this pinned source.

## Boundary

This is source/HIR correspondence evidence only. It does not resolve `Display`, consume the `where` premise, construct an imported scheme, implement multi-HIR inference, or claim either sample runs. The `[io]` contravariant open-row interpretation `[io,'e]` remains unchanged.

No source spelling intrinsic, selected method, altered source bytes, or new restriction is allowed. Existing errors/recovery remain fail-closed. The original public route resolver stays authoritative for export identity.

## Exact paths

- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this sprint contract
- `notes/theory/2026-10-22-r294-say-provider-carrier.md`

No other paths are leased. No subagents are used under the user's explicit solo-work instruction; dispatch is recorded as degraded solo dispatch.

## Evidence and stop point

Use the exact 40-module pinned closure and the same `ParsedFile` for export index and provider artifact. The test must distinguish the default HIR result from the LocalSource-aware HIR result, join the exact public `say` source declaration to its unique provider binding, and verify the binding's source carrier retains the declaration-owned `where 'a: Display` clause and parse-owned identities.

Run the focused pinned-owner test, `cargo check -p yu-playground`, `git diff --check`, and agent-sprint static checks. Stop after this source-carrier seam is characterized; keep imported typing, role evidence, runtime behavior, theorem closure, and production OPEN.

Superseded by `r294-say-provider-carrier-rev2-20261022.md` after the whole-module LocalSource probe exposed that `pub host act` roots cannot use that entrypoint.
