# Yulang Examples

These examples are small executable programs for the current implementation.

Run one with:

```bash
cargo run -q -p yulang -- --run examples/showcase.yu
```

Or run the smaller examples one by one:

```bash
cargo run -q -p yulang -- --run examples/01_struct_with.yu
cargo run -q -p yulang -- --run examples/11_attached_impl.yu
cargo run -q -p yulang -- --run examples/09_optional_record_args.yu
```

Print inferred public types with:

```bash
cargo run -q -p yulang -- --infer examples/01_struct_with.yu
```
