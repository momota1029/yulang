# R15 outcome — `CLOSED_COMPLETE_CONDITIONAL`

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15`  
Contract SHA-256: `eff6b4718b194b07e807db84872926565448b4baa86ae2fd02d3b052fcfcfc50`  
Input manifest SHA-256: `a57e78421e678f86c7c8aa225bb48970930a2984eb2198f5d5f0630482a30f96`  
Pre-close state archive SHA-256: `b538f8f8281b0b189cfe812e33aeb1ccfe3bfa5211a110f12a7bf00baa673dbb`

## Result

The R14 proof-construction failure in `control_test_fields` was repaired without changing its theorem declaration, quantifiers, hypotheses, definitions, imports or the rest of the module. The only diff against archived R14 artifact `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc` is the true-branch proof: it applies `loop_test_fields` at `drained constructor events s`, then simplifies the drain's `testFields` projection.

- R15 artifact `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean`: SHA-256 `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7`.
- Proof handoff: SHA-256 `1526bc3f0e426f3f08401a5190b494d6097d784599fbe8dc0ad61b305354f634`.
- Source handoff: SHA-256 `7500b0fe883f354387ed9298e2f7aa5b125bb8b89256769b5da3f9f9bb64a7ed`.
- Primary Audit 1: Lean 4.35.0, exit 0, 17.235 seconds, peak RSS 990096 KiB; all 38 inherited/current roots printed complete theorem types and transitive axiom reports. Aggregate receipt `/tmp/yulang-effect-permission-term-call-control-20261029-r15/attempt-1/audit-receipt.json`, SHA-256 `02eca0b48d30dd438a696cab015975bdcc89cc997e6e41df1108b453cb28378b`.
- Axiom sets: 14 roots with none; 21 with only `propext`; three with `propext`, `Classical.choice` and `Quot.sound`.
- Fresh independent compiler_referee review PASS, no BLOCKING/major/minor findings. Review handoff `tasks/agent-loop/inbox/effect-permission-term-call-control-r15-review.md`, SHA-256 `cb95407ad46dade0f011c30abb45b67788d96863f8e5e51becfbff51793ebb79`.
- The 168-entry R15 manifest, 17-file project copy, plan, tools, raw output and resource receipts authenticate without mismatch.

## Exact theorem and remaining boundary

The candidate establishes only the conditional source-directed control model in R14. The full 19-root R14 theorem set and inherited R12/R13 roots are kernel-accepted under their printed hypotheses and reviewed. This does not close the original inference/executor parent theorem.

Constructor/event generation, sampler availability and counter-state production remain explicit inputs. Actual Rust execution/state correspondence, test-configuration instrumentation, primitive/alias authenticity, complete source/consumer correspondence, native publication, original parent preservation, effect hygiene, soundness, principality, progress, termination and production remain OPEN. The R14 closeout remains `CLOSED_INCOMPLETE`; R15 supplies the reviewed proof repair and audit as a new conditional outcome, without retroactively replacing its frozen failure record.

No tests, Cargo, compiler code or production configuration were changed. No Git operation occurred in the proof/review lanes. All worker writes stopped; no descendants remain.
