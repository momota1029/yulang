# Replaying the role CST boundary

The checked-in Rust golden and the documented associated-type example are
different inputs. The former is an exact recorded Rowan dump from a current
Rust test. The latter was reconstructed from documentation and the actual
observed argument wrapper; it did not come from a parser execution.

From the repository root, with Lean dependencies and cycle 293 modules available:

```sh
python3 notes/verification/cycle293/check-rust-tags.py
PYTHONDONTWRITEBYTECODE=1 python3 notes/verification/cycle293/test-rowan-golden.py
python3 notes/verification/cycle293/test-json-cli.py
```

To produce the exact known golden wire again:

```sh
python3 notes/verification/cycle293/rowan-debug-to-wire.py \
  --golden crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs
```

To read the recorded golden at mixed child path `[0]`:

```sh
cd lean
lake env lean --trust=0 --run ../notes/verification/cycle293/run-unresolved-cst.lean \
  ../notes/verification/cycle293/recorded-rust-cst.json 0
```

The command only reads supplied CST data; it prints the unresolved spelling
`a`, binder `'x`, and its direct non-type member. Its success does not clear the
recovery recorded at the file's root after that role.

## Next validation with Rust

Rerun the exact golden test and use the additional proposed source cases:

```sh
cargo test -p yu-syntax role_method_signature_where_keeps_its_pre_wp17_recovery_cst
cargo run -p yu-syntax --example syntax_guide_check -- \
  notes/verification/cycle293/proposed-rust-role-cases.md --tree
```

The second command prints the source, diagnostics, a shape summary, **and**
the full Rowan Debug tree per Markdown block. Keep just one selected block's
`Root@...` tree and the exact matching source bytes (including final newline)
to use the versioned converter with `--debug <tree-file> --source <source-file>`.
The converter fails on unsupported Debug escapes or any byte mismatch.
It is a verification adapter, not the production CST serialization API.

The production interface should get the complete mixed child sequence from a
retained Rust parse result, map actual tags, preserve all token text, and
supply an independently fresh snapshot brand and selected ordinal path. The
CST producer does not assign semantic IDs or decide source-language validity.

The loader's small synthetic shape matrix can also be run:

```sh
python3 notes/verification/cycle293/test-cst-matrix.py
```

This is one Lean invocation over 42 supplied tag trees (visibility, trivia,
ordinary required/default shapes, missing RHS, missing Equals, multiple
direct children, and missing argument wrapper). It checks the allowed output
shape and the exact resulting direct member path, not parser acceptance.
