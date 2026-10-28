# NATIVE-WITNESS-FRAME-REPAIR/r9 outcome

Status: **CLOSED_INCOMPLETE**. Contract `d57ddde8ea97eff2f6641370b2d58d34c06c51398d16941b26a8244893e9783a`; 76-pin manifest `9268a0d7cd0eb3a674ba10fd2ec4dba63a25007c2f32fd513510ce44f47cc544`.

## Objective and reviewed outputs

R9 attempted only the R8 local Rust fixture-binding and Lean elaboration repairs. It preserved the original parent quantifiers, supported source domain, seven conditional theorem statements, every represented prefix, `WriteAll`, and the exact `extract` premise. It did not close `extract` or establish native/source correspondence.

- Rust candidate: `isolated/native-witness-frame-repair-r9/crates/yu-solver/src/candidate_scheme.rs`, SHA-256 `9701321450cda1500a7aa77c0417bcec4a502e006b3c080591a82b7831e9e4bb`.
- Lean candidate: `isolated/native-witness-frame-repair-r9/notes/theory/lean/YulangClosure/NativeExternalEffectFrameR8.lean`, SHA-256 `747150d9627b84830389ff1b088f43b78da64c3b1f432dbc868a7466b51d1ad9`.
- Proof handoff: `tasks/agent-loop/inbox/native-witness-frame-repair-r9-proof.md`, SHA-256 `47828798f2fd77a03c330dd0821426828bca634007a2d982848fe8fcb862095f`.
- Independent review: `tasks/agent-loop/inbox/native-witness-frame-repair-r9-review.md`.

The reviewer authenticated all 76 inputs, using unchanged R8 copies to authenticate the initial bytes of the two mutable output paths. It accepted the exact outputs for initial conditional checks, verified the fixture-local Rust repair and preserved Lean types/prefixes, then rejected checked-evidence acceptance after reviewing all eight retained log/resource files. Review was read-only and independent.

## Conditional checks

Only the two authorized initial attempts ran, sequentially. Both were pinned to CPU 0, sampled against a 2 GiB process-group RSS ceiling, and recorded in their exact leased files.

- Cargo 1.95.0 / rustc 1.95.0: exact focused fixture command, wall limit 90 seconds, exit `-15` at 90.0848 seconds (`WALL_LIMIT`), sampled peak process-group RSS 1,712,734,208 bytes. Stdout is empty; fixture execution is **NOT ESTABLISHED**. No source diagnostic was produced, so there was no Rust repair input.
- Lake 5.0.0 / Lean 4.35.0: exact `lake env lean -j1 -M1024 YulangClosure/NativeExternalEffectFrameR8.lean`, exit 1 after 3.1599 seconds, sampled peak process-group RSS 606,572,544 bytes. The diagnostic at line 208 reports ambiguous `.sink` notation. Four declarations report no axioms; `callback_frame`, `observed_capacity_frame`, and `native_frame_conditional` report `[propext, sorryAx]` after recovery. Checked theorem acceptance is **NOT ESTABLISHED**.

Retained log SHA-256 values:

```text
cargo-1.argv       e82890aea77224a0ddb15b2fbdaccc9f46dbd008a21688d94cb22019e2543812
cargo-1.stdout     e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
cargo-1.stderr     366e96526ba521a700cdc13f30b837aeeff47c02e43e59327676f64915a78b25
cargo-1.resources  5e40846ca46b23f32c4962a1e8c780fc9e127e228097e7615dccb4b919dc0f4a
lean-1.argv        f5b1eb40f3e9f98de9355192b556f384e248c6f9d51e0be7ea885b3b0c0d5b45
lean-1.stdout      8f5bb3dd27efeae958ccd58cf5eba6179f675347ee3ff0c4dbc4fa15494f4875
lean-1.stderr      e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
lean-1.resources   e7da42cf792fb6e409cf96c29c8c380dd2b9c81baa65646955c63d68090696a0
```

The unused second-attempt paths contain no execution evidence. The Cargo resource-boundary stop clause applies, so R9 admits no retries or repair. The proof owner stopped writing at 10:45:28 UTC within the original 600-second lane; no repair round was used. No checks or axiom audits ran after the final review.

## Remaining gates and disposition

`extract`, standard-library I/O realization, exact native trace coverage, source/native correspondence, `NativeCorrespondence`, `SourceProblem.InferenceSoundness`, effect hygiene, and production are **OPEN**. R8 remains `CLOSED_INCOMPLETE`; no earlier result is promoted.

The current authorized outcome is a record of failed conditional validation only. Any correction requires a newly admitted bounded packet with new check authority and an eligible proof owner.
