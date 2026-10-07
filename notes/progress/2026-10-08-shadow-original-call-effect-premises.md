# Shadow inventory for original Call-effect formation premises

Date: 2026-10-08
Status: M1 default-off shadow evidence plumbing; pre-write spec audit and post-write compiler-referee review passed
Baseline: `413c337bc0cdecaeb539829596fcd97521cf087b`
Authority: user-authorized shadow lane; reviewed original Call output minimal-clause note remains a candidate and is not adopted
Implementation authority: unresolved premises only

## Result

Each retained Apply now carries two additional unresolved premise markers:

- `SourceSignatureLocalImmediateCallEffectPositionFormation`
- `OriginalTypedCallEffectOccurrenceIntroduction`

They make the reviewed O0 frontier visible in the HIR shadow inventory and survive existing generic Core/solver joins by borrowing the exact HIR premise references. They do not form `H_eff`, a position `q_c`, an original typed occurrence `ce_orig`, or any incidence, scope, source association, typing, evidence or semantic relation. The dependent local scope and whole original `xi` remain unresolved. The existing separate `p_out(c)` leg and all prior premises remain intact.

The pre-write spec audit authorized only two pending rows per Apply and their dependent inventory-count updates. The post-write compiler-referee review passed the frozen 19-file change: it verified the per-Apply counts, preserved inventories and exact borrowed joins, and found no semantic discharge, production route change or DAG closure. The historical Frozen Oracle remains non-authoritative.

## Verification

The implementer ran the focused HIR shadow filter (74 passed), six Core targets (28 passed) plus `shadow_feature` (3 passed), two solver targets (5 passed), and two exact solver differential tests (1 each). Feature-off `cargo check -p yu-hir`, `git diff --check`, and formatting for the changed files passed except for one pre-existing formatting discrepancy at `crates/yu-solver/tests/shadow_f5_differential.rs:548`, retained to avoid unrelated drift. The independent reviewer reran `git diff --check` and did not rerun tests/builds.

No broad workspace suite, production inference check, performance measurement or semantic experiment ran. No DAG status changes follow: O0 remains open pending independent original signature-local position formation and a valid original typed-occurrence introduction.

## Changed paths

The frozen delta comprises `crates/yu-hir/src/shadow.rs`, its eight affected HIR tests, seven Core tests, and three solver tests. No other files were changed by the producer.
