# Contract v1 Diagnostics Evidence

This page records focused diagnostics evidence that sits outside the Contract v0
stable-core ledger. It is current executable evidence, not a roadmap.

## Run Parse Diagnostics Gate

The source of truth is:

```text
tests/yulang/cases.toml
```

Current run parse-diagnostics manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 1 | parse diagnostics stop execution before runtime roots |
| total | 1 | run route parse-diagnostics gate |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --case run_invalid_ref_assignment_syntax tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-04:

```text
contract cases ok: 1
```

The manifest case fixes the non-zero `run` exit and the user-facing parse
diagnostic. The negative assertion that runtime roots are not printed is covered
by the CLI Rust gate:

```bash
cargo test -p yulang --test cli compatible_run_rejects_syntax_diagnostics_before_execution -- --test-threads=1
```

The direct user route is:

```bash
cargo run -q -p yulang -- --std-root lib --no-cache run --print-roots tests/yulang/regressions/diagnostics/run_invalid_ref_assignment_syntax.yu
```

That route must emit `yulang.syntax`, exit non-zero, and stop before executing
the program.
