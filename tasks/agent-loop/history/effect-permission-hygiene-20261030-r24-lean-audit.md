# R24 Lean audit stop receipt — constructed but unchecked

- Sprint `ANNOTATION-HYGIENE-TRANSITIONS/20261030-R24`; contract SHA-256 `4fc63b868a8e61f8b4a5c1c59e6dccc4e8b6aa4e8e9afa24985c0408654ac39b`; baseline `9a74a70a32ebda716a00c7203d8e606343cf442a`; schema R1 digest `686c96c8f8b5417b075a18954f773ad4071996e51e809d65040a87441c342c3c`.
- Frozen final handoff `tasks/agent-loop/inbox/effect-permission-hygiene-r24-proof.md`, SHA-256 `e4725fd5cb9c22fce20a53da82443da5dc0b2f9aaab34157c0f624f32a59f101`; final candidate module SHA `4bb9eafe2c0f7123c4d43722083190b9f7c78c2e0f6661160c5ccc56da1f7083`; scratch artifact index SHA `f6a14546cd57ce6a1b4e928103bbf0e9204587b99f40648c132dcbbb40300e51`.
- Audit-1 input/module SHA `faf2cd3e3057e9caca18a33bc2cc38b3518a3be2e37e3fbeac029544d2602644`; final bounded repair changed only layout. Luna compared whole files after removing whitespace and got equal SHA `00d359cb1688990c129243f60908caa0af2c475bb010bcd5f62934d9e9054c6c`. Definitions, theorem statements, hypotheses and R1 meaning were preserved.
- Frozen checker archive SHA `b268f3dc276fef2d160c7729b586f23a8a037754ac62744aed17aee1a50d4ac6`; checker SHA `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6`. Both audits used all 22 selected theorem names, explicit isolated project and native Lean 4.35.0 Lake paths, CPU 0, a 55-second checker timeout and a 60-second wrapper cap. Commands are preserved and hashed in scratch; no manual checker bypass.

| Audit | Exit | Elapsed | Max sampled RSS | Log SHA-256 | Resource SHA-256 |
|---|---:|---:|---:|---|---|
| 1, module `faf2cd3e…02644` | 1 | 5.938590698 s | 923,385,856 B | `973d010c0633efcb4cdb22c536ccb09f56d58e937f62de837973662cb0c69f44` | `558782e15a725604564b848afec0540109ac28c95f6d8fda8e7bc7016388f37b` |
| 2, module `4bb9eafe…f7083` | 1 | 5.850906778 s | 929,808,384 B | `3e8e56b5dc242351a222d892a58705fde06cf3abb41cc832e7e280c1dbe02e4f` | `3fb1a47d8a7e3b0041b82c9beeecfed0e79115ef171f8b8b168cfa8d1996e7b1` |

Combined audit wall time `11.789497476s`; no wall/RSS guard fired. Audit 1 failed on multiline State-update parser/layout errors. After a whitespace-only layout repair, audit 2 reached case-pattern errors: `step_conserved` has six alternatives and `step_events_before` three alternatives with an extra leading State binder; `callbackRequest` receives five names when four are expected, shifting a proof argument into the `Execution` position. Exact diagnostics are in the frozen logs.

**No selected-module build succeeded. No theorem type or transitive axiom list was emitted for any of the 22 names; no `.olean` or checked theorem was delivered.** The candidate is constructed but unchecked and independently unreviewed. It proves neither native/source correspondence nor the original parent.

The proof worker `/root/r24_lean` stopped all writes/processes/descendants at `2026-10-29T18:53:29.419105Z`. Conservative charge to stop is `1,674/1,800s`; `126s` remain but the two-audit cap is exhausted and selector forbids another audit or diagnostic invocation. No Cargo ran or is authorized.

Selector's latest decision: freeze Lean as constructed-but-unchecked; do not change Rust leases or resume R2 after this failure. Any later work needs a new bounded decision/envelope. R2 remains byte-frozen and REJECTED by the independent compiler referee. Original A/B, source/native correspondence, effect hygiene, soundness, principality, termination and production remain OPEN.
