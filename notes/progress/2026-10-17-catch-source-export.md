# Catch source/export sprint: compile attempt receipt

Sprint: `source-matched-catch-action-and-export-20261017`, contract revision 7
SHA-256 `d5934a13375dc3207d2d166fac9f803451ede149576dbfdb760f84d6e0bac2d2`.
Baseline: `e0fa94e509d28eea9aa7d5884b5fa2b060363ca4`.

## Frozen inputs

- Conditional proof artifact: `notes/theory/2026-10-17-source-matched-catch-actions.md`
  SHA-256 `064e813a0bcf82019d9379dfa25fd1c825eabd2072c5933f32b28d6d1ea284ae`.
- Proof handoff: `tasks/agent-loop/inbox/20261017-source-matched-catch-actions.md`
  SHA-256 `61a5b4d5487871cb474e79148ac835dfaf01075ff3a54ef673cb71d02f9e6fda`.
- Final research example: `crates/yu-solver/examples/research_catch_source_export.rs`
  SHA-256 `325a6807cd2423bc941083264118138f51055cdf426506bb2a9e380f0b5b361e`.
- Binder repair handoff: `tasks/agent-loop/inbox/20261017-catch-source-export-binder-repair.md`
  SHA-256 `d3d659e557e0007f6978309e1ebf097fb5d4eaf89a6a6b08fd16c3e8c5765f0b`.
- The two prior example snapshots and both repair handoffs retain their exact
  hashes in contract revision 7; all 51 direct dependency pins matched before
  this one run.

## Sole authorized execution

Luna ran exactly once:

```sh
timeout 120s env CARGO_BUILD_JOBS=1 cargo run -p yu-solver --example research_catch_source_export --features shadow-apply-candidate
```

The command exited 101 after 2.17 seconds. Compilation failed before the
example executed. Rust reported E0308 at example lines 171 and 185: both calls
pass an owned `LocalSourceIndex` to `LocalSource::expression`, which requires a
borrowed `&LocalSourceIndex`. The compiler suggested borrowing
`&operation_arm.body` and `&value_arm.body` respectively. No parse, HIR, solve,
fresh-use or export observations were produced; those remain UNKNOWN.

The attempt stayed within the 120-second cap and consumed the sole Cargo
authorization. There was no retry, source change, test, or additional build.

## Interpretation and remaining gates

The source-matched proof conditionally constructs selected-request and normal
value-arm bodies for this exact specimen, while leaving
`CATCH-SPECIMEN-TYPED-INCIDENCE` open. The example has two mechanically
identified borrow errors. Since the contract authorizes no further repair or
run, the source/HIR/candidate observation outcome is partial and unresolved.
The compile failure says nothing about source acceptance, typing, handler
adequacy or candidate export behavior.

The original CHOOSE-SOURCE-2, F1, FK1, FIRST-RESULT-ADEQUACY, H1/H2, JOINT_DEC,
F5, source-Generalize/public-export, principality and production gates remain
OPEN under their original scopes. No compiler library or test expectation was
changed. Review is pending for this frozen example and exact run receipt.

## Independent post-execution review

A fresh regression auditor reviewed the frozen example, repair snapshots,
rev8 pins and this run receipt without rerunning Cargo. Disposition: CLEAN for
acceptance of the bounded compile-failure receipt only. All 52 direct dependency
pins matched. The reviewer confirmed that the source passes owned
`LocalSourceIndex` values at lines 171 and 185 while
`LocalSource::expression` requires `&LocalSourceIndex`; the saved compiler
output therefore matches the frozen source. No example code executed and no
parse/HIR/solve/fresh-use/export observation exists. The sole-attempt/no-retry
fact relies on Luna's run receipt and statement, not independent process-history
instrumentation. Requested Sol/medium; observed UNKNOWN/UNKNOWN; conservative
90-second charge; reviewer STOPPED.

Disposition: sprint `ENDED-PARTIAL-REVIEWED`. The proof artifact is a
conditional source-action construction with `CATCH-SPECIMEN-TYPED-INCIDENCE`
open. The implementation example remains research-only and fails compilation
at the two recorded borrow sites. No production code changed. CHOOSE-SOURCE-2,
F1/FK1/FIRST-RESULT-ADEQUACY/H1-H2/JOINT_DEC/F5/source-Generalize/public-export/
principality/production remain separately OPEN.
