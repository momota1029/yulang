# R248 — imported operator headers into the syntax environment

Status: implemented syntax integration slice; exact R149 samples remain OPEN. No independent review claimed.

## Root-cause correction for R247

R247's Console diagnosis incorrectly attributed `say:` to root colon parsing. The exact R149 Console input is 92 bytes; its reported syntax error at bytes `88..91` covers `+ 2`. The isolated expression `say: 1` has no syntax diagnostic, then stops as unsupported candidate source. `say: 1 + 2` has a syntax diagnostic without the imported `+` declaration. Supplying a source-local `pub infix (+) 5.0.0 5.0.1 = \\x -> \\y -> x.add y` removes syntax recovery and advances to unsupported candidate source. Thus the R247 claim about `MlMode::None` was wrong. The first syntax seam is that the playground supplies an empty `SyntaxEnvironment`, so the library's dynamic `+` operator is absent.

The R149 source evidence locates the operator declaration in `std/core/ops.yu:29`, blob `575e6fb15ce2d91a39004bbc7b842fedb2d83fdf`. The Console CLI currently constructs `SyntaxEnvironment::empty()` in `tools/inference-playground/src/lib.rs::prepare`; no standard-library source resolver feeds imported operator headers to it.

## Implementation

`SyntaxEnvironment::from_imported_headers` now builds imported operator capabilities from already scanned `HeaderInfo` values paired with dependency slots and provenance. It preserves the imported source range and `OperatorOrigin::Imported(slot)`, rejects dependency slots without provenance, rejects same-fixity conflicts while retaining both source origins/ranges, and excludes non-public operator declarations. `OperatorDeclaration::imported_at_range` is available in normal builds, and the header conversion uses it instead of manufacturing local origins.

The syntax-environment tests cover imported source/range identity, the unchanged 92-byte R149 Console text parsing without syntax recovery when the `+` header is supplied, missing dependency provenance, conflicting imports, and exclusion of private declarations. The constructor accepts headers that a caller has already scanned and authenticated; it does not implement module resolution, import/re-export visibility closure, or source revision authentication itself.

## Verification

- `cargo test -p yu-syntax syntax_environment::tests`: 8 passed before the final test fixture was changed to the exact 92-byte Console source.
- `cargo test -p yu-syntax imported_header_operator_selects_parser_capability_with_source_provenance`: 1 passed after that exact-source change.
- `rustfmt --edition 2024 --check` on the three edited Rust files: passed.
- `git diff --check`: passed.
- `cargo fmt --check` and `cargo fmt --check -p yu-syntax` were also inspected; both report existing formatting differences in unrelated files. They did not modify files.

No sample was semantically accepted or executed in this packet. No Yulang2 module resolver, imported `SemanticImports`, tuple/type/role inference, whole-module schedule, host write, public Types pane, or Web/WASM path was implemented. Existing sample outputs and expectations remain untouched.

## Next required work

The syntax environment still depends on an upstream source owner to load the actual pinned module headers and resolve transitive import visibility. The next implementation must join that source resolver with `SemanticImports` and the selected source set; hardcoding `+`, adding it as a local declaration, or treating a syntactic parse as Console success would violate R149. Types still stops at comma-tuple source formation. Keep the original R149 outcomes and parent A/B, R70/R71/R72, soundness, principality, and production gates OPEN.
