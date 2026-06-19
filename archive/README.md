# Archived Yulang Artifacts

This directory keeps retired Yulang code, notes, and research material as
reference-only artifacts. Current implementation work lives outside `archive/`.

The archived crates are not maintained as standalone build targets. In
particular, path dependencies inside `archive/crates/*` may still reflect their
old workspace layout.

## Crates

Retired crates live under `archive/crates/`. They are intentionally outside the
Cargo workspace.

Current crate work lives under `crates/`:

- `sources`
- `infer`
- `poly`
- `specialize`
- `mono`
- `mono-runtime`
- `control-vm`
- `yulang`
- shared crates: `parser`, `list-tree`

## Notes

Retired design notes, handoff reports, refactor audits, and archived TODO tracks
live under `archive/notes/`. These files may still be useful as history, but
they should not be treated as current plans unless an active note links to them
explicitly.

## Papers

Old CPS/native-backend paper snapshots live under `archive/papers/`. The current
type-inference reference paper that is still used by the spec remains in
`spec/`.
