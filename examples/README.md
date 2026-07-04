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
yulang run examples/11_attached_impl.yu
yulang run examples/12_cast.yu
```

Config/file/text cookbook examples:

- `examples/config-file-text/config_read.yu` — read a mixed-spacing `.conf` file and parse the port.
  ```bash
  yulang run examples/config-file-text/config_read.yu
  ```
- `examples/config-file-text/file_edit.yu` — edit todo lines through a durable text ref copy.
  ```bash
  yulang run examples/config-file-text/file_edit.yu
  ```
- `examples/config-file-text/log_stats.yu` — summarize access-log lines with parser-pattern captures.
  ```bash
  yulang run examples/config-file-text/log_stats.yu
  ```

Effect-inference notes and small `dump-poly` inputs live under
`examples/effect-hygiene/`.

Use `check` to type-check a file and print inferred public types:

```bash
yulang check examples/01_struct_with.yu
```

From a repository checkout, the same commands can be run through Cargo:

```bash
cargo run -q -p yulang -- run examples/showcase.yu
cargo run -q -p yulang -- check examples/01_struct_with.yu
```
