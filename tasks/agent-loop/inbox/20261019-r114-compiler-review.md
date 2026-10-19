# R114 conditional partial compiler/source review

Verdict: **CLEAN for the expressly conditional runtime permission-consumer claim
only.** No BLOCKING, major, or minor correctness finding within that scope.
This does not certify distinct source IDs, the complete source path, CLI
execution, a language-level rejection, or a general hygiene theorem.

Reviewed R114 rev1 contract SHA-256:
`7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
Proof note SHA-256:
`447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92`.
Handoff SHA-256:
`1e557c2adbcf53861701fa0a11679124fde1ebf87606a35624c923be6eba3f18`.
All 19 contract pins match.

Independent source inspection confirms the conditional trace. Given authentic
distinct signal/other family IDs, `source_annotation.rs:193,274,529` and
`local_source.rs:601,1091` retain the row/operation identity. `program.rs:488`
projects the original formal; `receiving.rs:22` clones its schema after root
and type checks; `machine.rs:979` installs the computation boundary. With
receiver row `[other]` and request family `signal`,
`receiving.rs:258–267` makes `local_grant` false. The program's constructed
Lambda excludes the closed-primitive bypass (`primitive.rs:35`,
`program.rs:748`). Conditional on reaching the matching Catch with this
installer boundary, `machine.rs:1582–1591` returns `HandlerEvidence` at the
handler site. `lib.rs:183` returns the unavailable error before result
rendering; `main.rs:75–90` emits errors on stderr and failure status.

The exact owner needed to prove that distinct declaration nodes mint distinct
`SourceNodeKey`s is outside the frozen pins: `module.rs:1110,1123,1135,1148`
delegates key production to `source_identity::{source_keys,try_source_keys}`.
That owner was not read. Distinct IDs and exact request/catch reachability
remain OPEN. The review therefore accepts only the conditional consumer
argument; it grants no pin expansion or command clearance.

Review was by fresh read-only `/root/r114_partial_compiler_review`. The reviewer
returned CLEAN but did not write because its role is read-only; Luna transcribed
the verdict. No tests, builds, runtime/CLI/compiler commands, Git or writes ran.
