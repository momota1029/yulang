# R5 read-only source reconciliation

Sprint: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r5`  
Owner: Luna, read-only source lane (50-second limit).  
Input manifest SHA-256: `79112990c69fd83f10b71d25b3ea5cdb4cbde68a3abddfb2e00dc9675159f595`.

## Pinned source correspondence

The R5 manifest rechecks the R4 pinned source owners and exact failed R4 receipt. Current source hashes match the manifest: `candidate_effect.rs` `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`, `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`, `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`, and `candidate_scheme.rs` `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. No Rust source changed.

R4's source-to-observation crosswalk remains applicable. The formal owner derives Definition scope. The fixed tree has the root Tuple row plus the two Function result rows, with the four actual constructor Effect-port visits in order: first omitted argument, first negative concrete result, nested omitted argument, nested negative concrete result. Value/tuple traversal contributes no additional effect allocation for these atomic leaves. `fresh_effect_at_level` returns the pre-push ordinal; each of the four ports allocates once, giving `n,n+1,n+2,n+3`. The observed first origin 22 entails slice base 21; this is not the solver's global initial state.

The exact observation retains rows 22/24 on the two result paths, concrete operands `[1]`/`[2]`, capture 4, root 0, and negative graph nodes 17/14. R4's explicit source projection maps the observed Int/Unit leaves, Function children and argument/result rows to the decoder instructions. The independent R4 review accepted that bounded static correspondence and found no additional concrete defect.

## Boundary

This lane reuses R4's source extraction; it does not claim the R5 Lean declarations have elaborated or have complete type/axiom receipts. Those remain gated on the separately released R5 audits and fresh review. The output export, complete native execution, native State/scalar identity, parent A/B claims, effect hygiene, consumer residual, unequal transport, and production gates remain **OPEN**.

No Cargo/compiler/test command ran. No compiler source, Lean proof, dependency or configuration was changed in this source lane.
