# Sprint R293 — imported export to provider HIR ownership

Status: solo implementation checkpoint; source identity only; parent R149 stays open.

## Goal

Connect an already resolved `SourceExportResolution` to the exact public
declaration retained by one of the supplied provider HIR modules. Establish the
value binding owner for pinned `println` and the role owner for `Display`. Probe
`say` explicitly and record a missing provider HIR owner as an open seam.

The join must match module path, source key, syntax kind, exact range, exposed
name, and public visibility. Missing, duplicate, stale, recovered, or unsupported
owners fail closed. This adds no imported type/scheme, role conformance,
implementation selection, candidate constraint, or runtime behavior.

## Source and proof boundary

The source export resolver remains the authority for the public route. This
step joins its direct declaration identity to provider HIR and proves only that
the returned owner is the unique exact source-owned declaration in the supplied
finite HIR set. It does not prove that the Yulang2 import/type/role rules are
implemented by this HIR API.

The original R149 outputs, samples, proof obligations, and `[io] = [io,'e]`
meaning remain unchanged and open.

## Exact files

- `crates/yu-hir/src/module/source_exports.rs`
- `crates/yu-hir/src/shadow.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r293-imported-export-hir-owners.md`

No other paths are leased. No subagents are used under the user's explicit
solo-work instruction; sprint selection is recorded as degraded solo dispatch.

## Verification and stop boundary

Run the focused `yu-hir` and pinned-playground ownership tests, `cargo check -p
yu-hir`, `git diff --check`, and the repository agent-sprint static check. Treat
these as implementation/source-identity evidence only. Stop this bounded slice
after recording any mismatch; do not widen into type inference or method
selection without a new exact owner/dependency map.
