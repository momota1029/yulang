# R177 sequential pin correction

R177's frozen rev3 contract SHA-256 is `e3279f46a5076e833d3407b0a64214888fe443bd95badbb1c83a37c444c6af31`; its source and proof handoff hashes are `36f0ff4757d2881fa7383b807df3a915990f1c213445075ebfd2d6633bf0a877` and `b5ab4b8ac2deb186aec7eb7b87b0fde02967af59179e2706bb8b7d8414062154`. The original activation receipt remains byte-preserved at SHA-256 `41123e34dbd556caa9580b0528ae6ba6c260eb4633210670feddd156022a8feb`.

A strict follow-up audit found the rev3 `candidate_scheme.rs` pin malformed (63 hex characters): `6072c73bc1a1629f025cfbeba147c55898fea5d27463c490db2875b05308fec`. Its actual SHA-256 is `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`. The source handoff's candidate-scheme-specific details and prior review's blanket “all 30” confirmation are unauthenticated under rev3. The proof lane did not read this Rust file. The prior aggregate hash claim is withdrawn.

The source-to-original-App blocker remains independently supported by the properly pinned `shadow_apply.rs` and original Lean source rules, subject to fresh review. No source-qualified counterexample or theorem is established. R177 remains INCOMPLETE; `InferenceSoundness` remains OPEN with its original domain and shared witness.

This addendum is sequential evidence only. It does not rewrite the frozen contract, handoffs, or prior review. A fresh independent auditor must identify exactly which source-handoff claims depend on the malformed row, check every other R177 pin strictly, and assess whether the original-App blocker remains supported by authenticated inputs. No code, test, build, Lean or Git action is authorized by this correction.
