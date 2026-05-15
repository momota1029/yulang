# Native Example Sweep 2026-05-15

Command shape:

```bash
timeout 20s bash -lc 'RUSTC_WRAPPER= cargo run -q -p yulang -- native <example>'
```

## Passing

| Example | Native path | Observed output |
| --- | --- | --- |
| `examples/01_struct_with.yu` | default CPS repr (`closure value`) | `25` |
| `examples/02_refs.yu` | default CPS repr (`thunk boundary`) | `(22, 22)` |
| `examples/04_sub_return.yu` | default CPS repr (`closure value`) | `5` |
| `examples/05_undet_all.yu` | default CPS repr (`closure value`) | `[5, 6, 7, 6, 7, 8, 7, 8, 9]` |
| `examples/07_junction.yu` | default CPS repr (`closure value`) | `1` |
| `examples/08_types.yu` | default CPS repr (`closure value`) | `42` |
| `examples/09_optional_record_args.yu` | default CPS repr (`closure value`) | `6`, `2`, `12`, `12` |
| `examples/11_attached_impl.yu` | default CPS repr (`closure value`) | `(10, 0)` |
| `examples/12_cast.yu` | default CPS repr (`closure value`) | `7` |
| `examples/13_console.yu` | default CPS repr (`thunk boundary`) | `hello from Yulang`, `0`, `3` |
| `examples/showcase.yu` | default CPS repr (`closure value`) | `7`, `[2, 3, 4]`, `5`, `5` |

## Known Failing Or Mis-Matching

| Example | Current behavior | Tracking |
| --- | --- | --- |
| `examples/03_for_last.yu` | forced/default CPS repr times out on open-range `for` with local `last` | `notes/bugs/native_open_range_for_last_returns_payload.yu`, N9 |
| `examples/06_undet_once.yu` | fails before native with `expected (), got int` | `notes/bugs/index.md` frontend/runtime note |
| `examples/10_effect_handler.yu` | forced/default CPS repr returns a raw pointer-looking integer instead of `(9, "3\n6\n")` | `notes/bugs/native_effect_handler_tuple_result_prints_pointer.yu`, N10 |

## Smoke Checks Added Around This Sweep

- `runs_for_loop_return_escape_through_cps_repr`
- `runs_finite_for_loop_last_through_cps_repr`

These distinguish the fixed finite/open-range `return` escape and finite-list
`last` behavior from the remaining open-range local `last` problem.
