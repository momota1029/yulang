# Native signature observer

This standalone research executable observes the captured candidate graph for
the three fixed fixtures below. It uses the existing parser, retained HIR and
public `shadow_apply` API; it changes no compiler inference behavior.

The source is preserved byte-for-byte from the independently reviewed observer
at `/tmp/yulang-native-signature-observer-20261103/src/main.rs`, SHA-256
`cb33d461e2559c163484a3c23713976ca47e4cccd8e1fa62f3c726775ac30bfb`.
The original frozen crate baseline was
`40e0c52e458aaf268357038b259d6619d3ba5dae`. This package uses repository-relative
crate dependencies and its own lockfile. Reproduction against a different crate
revision is evidence for that revision only.

From the repository root, build with a private target directory:

```sh
CARGO_TARGET_DIR=/tmp/yulang-native-signature-observer-target \
  CARGO_BUILD_JOBS=1 CARGO_PROFILE_DEV_DEBUG=0 \
  cargo build --offline --locked \
  --manifest-path tools/native-signature-observer/Cargo.toml
```

Run the fixed positive fixture and both negative controls:

```sh
/tmp/yulang-native-signature-observer-target/debug/native-signature-observer \
  positive tools/native-signature-observer/fixtures/positive-nested.yu
/tmp/yulang-native-signature-observer-target/debug/native-signature-observer \
  negative tools/native-signature-observer/fixtures/negative-r301.yu
/tmp/yulang-native-signature-observer-target/debug/native-signature-observer \
  negative tools/native-signature-observer/fixtures/mutation-negative-concrete.yu
```

Each command must exit zero. The positive run checks the actual HIR declaration
Arc, same-parse source keys, exact definition root, captured Function children,
and effect Support provenance. It selects the unique outer Function through
root value bounds. Its root result effect retains ordered families `[E,F,E,F]`;
the returned Function result effect retains `[E]`. `same_identity` on captured
rows means session identity plus canonical representative, not raw row allocation
identity. Printed ordinal IDs apply only within the individual run.

Packaging validation rebuilt the executable offline with this package's lock
and ran all three fixtures successfully. All 326 frozen baseline crate files
matched the current repository. Using the original scratch fixture paths
reproduced the reviewed logs byte-for-byte; using the packaged fixture paths
changed only the printed input/module path. That path change represents a new
module identity and is not a cross-run identity assertion. No source fixture
or observer source bytes were changed during packaging.

Both negative runs check that candidate solving returns an error before graph
export. `negative-r301.yu` preserves the complete original R301 fixture and has
multiple unsupported features, so its rejection cannot be attributed to a single
cause. The other fixture changes the positive source's negative callback row
from `['arg]` to `[E]`. The executable is a fixture-specific assertion harness;
it is not a general source-file exporter.

The observation does not establish variable-spelling-to-row equality, direct
native-Term-to-captured-node equality, construction history, Rust–Lean
equivalence, original semantic admission, or R159/IF/Union parent closure. Source
parsing and graph capture are shared trusted machinery, not an independent
semantics oracle.
