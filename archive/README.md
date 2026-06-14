# Archived Yulang Crates

This directory keeps retired Yulang crates as reference-only code. It is
intentionally outside the Cargo workspace.

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
- `yulang`
- shared crates: `parser`, `list-tree`
