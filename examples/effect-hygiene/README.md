# Effect Hygiene Examples

These examples are small source files for explaining Yulang's hygienic effect
inference. They are intended for `dump-poly` / `check`, not as a single runtime
tour.

From the repository root:

```sh
timeout 120s cargo run -q -p yulang -- dump-poly-std examples/effect-hygiene/01_higher_order_inference.yu \
  | rg '^d[0-9]+:(apply|twice|use_int):'

timeout 120s cargo run -q -p yulang -- dump-poly examples/effect-hygiene/02_local_sub_handler.yu \
  | rg 'sub.sub|sub.return|note.tell|use_int|use_str|use_residual'

timeout 120s cargo run -q -p yulang -- dump-poly examples/effect-hygiene/03_data_position_private_tail.yu \
  | rg '"box.handle"'
```

What to look for:

- public signatures show ordinary effect rows;
- residual rows are preserved instead of erased;
- private stack evidence such as `#...` or `AllExcept(...)` does not appear in
  public signatures.

The full `dump-poly` output may include a `detached` debug section with internal
evidence. For these examples, inspect the public definition lines above the
detached section.

The broader explanation is in `docs/effect-inference-brief.md`.
