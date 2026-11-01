# R133 source candidate and STOP receipt

## Reconstructed target

Reconstructed in memory from pinned commit `cd460e0faf2c9ba2ba21a10f3dd83ed7bb1f4609` only. No Rust source file was written.

- `crates/yu-solver/src/shadow_apply.rs` baseline: 275,872 bytes; SHA-256 `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`.
- Reconstructed target: 275,970 bytes; SHA-256 `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`.
- `crates/yu-solver/src/candidate_scheme.rs`: SHA-256 `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`.
- `crates/yu-solver/src/candidate_intrusion.rs`: SHA-256 `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`.

The pinned `Graph` type declares `lambda_argument_effects: Vec<LambdaArgumentEffectCapture>`. Both affected fixture literals initialize this field with `Vec::new()`. The field follows `nodes` in the two literals, matching the pinned Graph field order and the required target hash.

The launch message suggested placing the field after `negative_formal_roots`. That placement produced a different SHA-256 (`9d163033758256aaca5e1d55b9b668b5ce2a7e2114b2d2f45a6a661ed17b603e`). The R133 owner confirmed the hash-matching placement after `nodes` and confirmed the contract does not require another field order.

## Complete unified patch

```diff
--- a/crates/yu-solver/src/shadow_apply.rs
+++ b/crates/yu-solver/src/shadow_apply.rs
@@ -4953,6 +4953,7 @@
             owned_regions: Vec::new(),
             negative_formal_roots: HashMap::new(),
             nodes: Vec::new(),
+            lambda_argument_effects: Vec::new(),
             tuple_children: Vec::new(),
             record_fields: Vec::new(),
             variant_alternatives: Vec::new(),
@@ -5066,6 +5067,7 @@
             owned_regions: Vec::new(),
             negative_formal_roots: HashMap::new(),
             nodes: Vec::new(),
+            lambda_argument_effects: Vec::new(),
             tuple_children: Vec::new(),
             record_fields: Vec::new(),
             variant_alternatives: Vec::new(),
```

Reconstruction comparison confirms exactly these two field additions; every pre-existing fixture value and assertion remains byte-identical. No source, generated, scratch, or build output was created.

## STOP receipt

- Assignment: R133 Luna/high implementation lane; requested model/effort: Luna/high. Runtime model identity was not independently introspected in this execution environment.
- Work stopped at the finite assignment bound after reconstructing the candidate and writing this handoff.
- No compiler, Cargo, tests, Lean, checker, storage/environment probe, working-tree diff inspection, or Git mutation was run.
- New path: `tasks/agent-loop/inbox/effect-permission-graph-fixture-initialization-r133-source.md` (this leased handoff only).
- Disposable scratch paths: none.
- Candidate remains uncompiled and untested; independent read-only review is still required. This receipt is not a review or theorem/source/native closure.
