# Yulang Examples

These examples are small executable programs for the current implementation.

Japanese: [README.ja.md](README.ja.md)

Start with `showcase.yu` for a broad tour:

```bash
yulang run examples/showcase.yu
```

Useful smaller examples:

```bash
yulang run examples/13_console.yu
yulang run examples/01_struct_with.yu
yulang run examples/04_sub_return.yu
yulang run examples/06_undet_once.yu
yulang run examples/10_effect_handler.yu
yulang run examples/12_cast.yu
```

`examples/11_attached_impl.yu` documents the intended attached-impl surface,
but it is currently kept as a type-checking/design fixture while role-method
runtime specialization is being tightened.

Use `check` to type-check a file and print inferred public types:

```bash
yulang check examples/01_struct_with.yu
```

From a repository checkout, the same commands can be run through Cargo:

```bash
cargo run -q -p yulang -- run examples/showcase.yu
cargo run -q -p yulang -- check examples/01_struct_with.yu
```
