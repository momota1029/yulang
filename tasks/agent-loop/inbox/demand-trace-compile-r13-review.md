# DEMAND-TRACE-COMPILE/r13 final review receipt

Verdict: **ACCEPT retained Cargo-1 evidence; CLOSED_INCOMPLETE.** The focused fixture compiled and ran, then failed with `ReceiptMismatch`. This is a bounded diagnostic result. It does not establish solver correctness, authorize a semantic repair, or close a parent gate. Runtime failure ends this sprint; Cargo-2 is not authorized.

## Authentication and resource result

The reviewer authenticated the exact contract, all 434 manifest pins (with only the two expected mutable source exceptions matching their frozen hashes), the candidate, `shadow_apply.rs`, rev2 handoff, and retained logs. Candidate SHA-256 `0ca44b920d30e0a596584c9c4ad5e2a61fdd9115fe1eaaf4346ff64d0776afef`; `shadow_apply.rs` `8db4bae1b79959161b6b0dc4d516164b0e756eb8cbc73896bb4a4545a0b0ebf8`; handoff `40229f9eb85e12bc90865e1997a299037dbb6990091356965ff4953504537953`.

The argv matches the contracted command. Cargo/rustc were 1.95.0. Exit **101**, wall **88.4893/120 seconds**, sampled CPU **45.84 seconds**, sampled process-group RSS **1,839,558,656/2,147,483,648 bytes**, CPU affinity **0**, no limit termination. Stdout records **0 passed, 1 failed, 816 filtered out**; stderr shows compilation and test launch. Warnings remain in stderr.

Log SHA-256 values:

- argv: `7361b29dc8d288dc2f1746fcf1c6793aef866d7fa8f956ba47843b5ad33e7aec`
- stdout: `148a99a6453e583317fadbb43b24660060f3e5725816d27aeaed5a2bc0c4e199`
- stderr: `caa03d84c01e3a0a16ddedfe4817cbe6b96636c5487f29356f74054f4d2ad84e`
- resources: `c4f09502a3f51b88ab7d489a82fe3b2918741cce76eb1920f03bd4cad5a7b8d9`

## Bounded trace finding

Within invocation 1, capture graph 3 interns negative demand root `TermArenaBrand(1):264` and returns node 11. FreshUse in that same graph reaches bound ordinal 3, relation 8, with a negative source bound whose upper endpoint is that root and whose captured upper index is 11. Demand fields agree across capture and FreshUse: original call 0, use instance 0, output scope 1, input route 0. FreshUse context use is 1.

Before root lookup, the reconstruction map has length 0; the actual lookup returns `None`. `candidate_scheme.rs:4658` returns `ReceiptMismatch`, and the unchanged fixture unwrap panics. Graph 1 is a separate capture; graph 3 alone provides the relevant same-capture join.

The source print identifies expression 1 and occurrence ordinal 2, but debug output hides owner and occurrence identity fields. The antecedent has admission/emission heads 6 and `EvidenceCoverage { gaps: 56 }`; imported antecedent construction was not reached. The trace does not establish the source Call/shared-witness law, complete antecedent authentication, or authority to insert a map entry.

No new blocking or major finding against retained evidence. Review was read-only; no reruns, writes, Git mutations, or descendants. Review stopped within the original 300-second budget.
