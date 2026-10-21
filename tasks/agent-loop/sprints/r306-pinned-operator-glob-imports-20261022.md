# Sprint R306 — retain pinned operator glob imports

Status: READY, solo Luna primary, no independent review; parent R149 remains OPEN.
Baseline: `aedb4d6e6` on `research/simple-sub-intrusion`.
Parent: unchanged Yulang2 Types and Console samples and original source/native obligations. Preserve exact source bytes and established import/operator semantics.

## Outcome

Make header import projection and pinned syntax-dependency planning retain valid module glob imports from the exact pinned Yulang2 source. For `lib/std/core/fmt.yu`, `use std::core::ops::*` must reach the syntax dependency environment with its exact module label and revision. Reparse the unchanged source and trace the original `Display.say` `+` occurrence to a real HIR operator use with the R305 declaration-site provenance receipt.

R305 found that the header scanner exposes only `std::num::frac::frac` from fmt's four leading imports. The three glob imports (`std::core::ops::*`, `std::data::opt::*`, `std::num::*`) are absent. Because `std::core::ops` is not selected, the original `+` token is a direct root token without an expression CST/HIR owner. This sprint addresses that exact missing source route, not operator meaning or member selection.

## Required evidence and falsifiers

- `scan_header` retains all four exact fmt imports with module route segments and the proper separator shape; the `*` selection must not become a fake module-name segment.
- `syntax_environment_for_source` selects the pinned module dependencies including `lib/std/core/ops.yu`, preserving its pinned blob revision and deterministic dependency slot.
- The same fmt bytes then parse without source recovery at the original `Display.say` `+`; its HIR `OperatorUseProvenance` reports Infix, Imported(slot), the selected `core/ops` label/revision and an exact provider range covering the pinned `pub infix (+)` declaration.
- A named import remains a named import with its exact route. An unresolved glob, wrong namespace separator, recovered import or missing provider fails closed rather than selecting another module by spelling.
- Run focused header import tests, the pinned fmt role/source test, `cargo check -p yu-syntax`, `cargo check -p yu-playground`, and the unchanged Types boundary regression. These checks are implementation/source evidence, not a theorem or independent review.

No operator rewriting, binding-power/fixity changes, imported-value resolution, candidate lowering, runtime change, or pinned-byte edit. If glob route representation is not source-authenticated by the current CST, stop and record that exact premise before changing source semantics.

## Proof correspondence and remaining parent work

Trace the original `use` source nodes into `HeaderInfo`, then the resolved pinned module source/revision into `SyntaxDependencyProvenance`, the accepted fixity site and original HIR operator occurrence. This proves only import and operator-site provenance. It does not identify the operator declaration's value owner, type the body, or establish Capture completeness or a source/native theorem. Preserve source identity separately from candidate endpoints; keep all original A/B claims and quantifiers.

Operator value owner, member candidate scheme and receiver prerequisite, settled implementation selection, method body inference, unchanged Types/Console execution, complete tuple publication/runtime, source/native proof, independent review, principality, termination and production remain OPEN. R149 remains OPEN.

## Exact leases and resources

`crates/yu-syntax/src/declaration/use_decl.rs`, `crates/yu-syntax/src/header.rs`, `crates/yu-syntax/src/lib.rs`, `crates/yu-syntax/src/tests/header.rs`, `tools/inference-playground/src/pinned_stdlib.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r306-pinned-operator-glob-imports.md`, and Luna-owned `tasks/agent-loop/current.json`.

One serial primary process, 1800-second cap, no carryover, no background work or subagents. Existing UNKNOWN worker leases stay quarantined. Luna alone stages and pushes. No independent reviewer is assigned under the explicit solo constraint; all evidence stays unreviewed. Stop when leases or the source route require another language/semantic boundary.
