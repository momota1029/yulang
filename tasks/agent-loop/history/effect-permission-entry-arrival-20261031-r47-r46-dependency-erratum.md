# R47 dependency erratum: R46 review and outcome

R47 remains under its frozen contract. It pins R46 review `7fbaed174bee5cae7a92874ddd795b9b80ec1bc8cd7f18acc30e6dedfde7c56e` and outcome `512e2afbe9f5f6ac12279b587fb6c2453f78bed1254ba4eff33fd69ea3395f14`, both reproduced at baseline `8017b53f5` by exact-path hashing.

Current corrected hashes are review `6e4080fe9a7b35a23e93bfebc793f15e8652403df98279fec36fd299e8312090` and outcome `1edec9719f82f14f25c6ceaea3e858b68ba312c5fb417b8b985653dea3faa430`. Verified delta: the review fixes only the `candidate_context.rs` hash transcription; the outcome changes only the review-hash reference. Review verdict, reasoning and source scope are unchanged. Keep the R47 contract unchanged and resolve its frozen dependencies through `8017b53f5:<exact path>`.

R47 Lean author read the pinned review before correction; proof imports R39/R45 only. Rust author read corrected review only and inventoried the outcome hash; neither informs the join implementation. Independent reviewer must verify this provenance.
