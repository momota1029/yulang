# Archived Yulang Implementation

This directory keeps the old `yulang` implementation as reference-only code.
It is intentionally outside the Cargo workspace.

The archived crates are not maintained as standalone build targets. In
particular, path dependencies inside `archive/crates/*` may still reflect their
old workspace layout.

Current work lives under `crates/`:

- `sources`
- `infer`
- `poly`
- `specialize`
- `mono`
- `mono-runtime`
- `control-vm`
- `yulang2`
- `yulang-lsp`
- shared crates: `yulang-parser`, `yulang-list-tree`
