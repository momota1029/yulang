# Sprint R253 — source-reachable receiver-ancestry renewal

Status: ADMITTED under the unchanged full goal: Yulang inference soundness and its Rust implementation. Preserve original parent theorems, Simple-sub A/B, accepted source domain, quantifiers and semantics. Parent delta remains zero unless a justified result is applied at the unchanged original edge.

## Fixed outcome

R252 was independently reviewed PASS. It proves finite row-erased Value template support and a raw-row-dependent finite-prefix bound `C_t <= 2*q_t*U(q_t)`, where `q_t=P0+B_t`; this is not an entry-only bound. Projecting raw row leaves to strict Parent ancestry yields an entry-finite descriptor carrier but no uniform receiver/pair fiber multiplicity. R252 identifies two guarded same-level receiver equations: later source-link replay and Function Result replay after extrusion. Neither equation is an accepted source-reachable repeated-credit trace. `R252-RECEIVER-ANCESTRY-1` remains open at `R70-DRAIN-1` / `NEWPAIR251`.

Resolve source-reachable renewal through those actual guards using path-sensitive symbolic execution and cutpoint induction. Track exact raw receivers, structural selectors, input fibers/heads, processing contexts, complete-pair rewrite states, replay frontiers/dependencies and canonical representatives. Analyze source-link replay and Function Result ports, selected-bound returns to template roots, other structural ports and merge/canonicalization. Either prove an entry-uniform receiver-ancestry/fiber multiplicity bound and apply it to R252's entry-finite carrier, then R251 births and R250 merges; or freeze the first precise guard equation that blocks renewal.

If claiming a collision, backward-realize it from an accepted source constructor prefix and exhibit a finite source-qualified trace exceeding the **explicit proposed multiplicity**, with every enqueue, context, memo, replay and representative guard justified. A finite collision refutes only that candidate bound, not termination. Conditional arrows, shared source labels, synthetic cycles, resource exhaustion or missing proof are not counterexamples. Do not claim divergence, defect or semantic need for global sharing without evidence. Keep relation/context/fiber closure, eventual Diagnostics/return and unrelated obligations separate.

Implementation lane: Luna/high, **NO_SAFE_CODE_SLICE**. No production edit absent a concrete accepted-source violation of an approved clause.

## Assignment, leases, inputs and limits

One registered `prover`, Sol/high, worker `/root/sol_r253_receiver_ancestry`, no descendants; maximum 2,400 active seconds across at most three substantive stages. Exact write leases:

- `notes/theory/2026-11-02-receiver-ancestry-renewal-r253.md`
- `tasks/agent-loop/inbox/receiver-ancestry-renewal-r253.md`

Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git.

Frozen source-baseline HEAD before the R253 admission checkpoint:
`901d1f9222c0c672e5d50dfb7beb29d74d1e5925`. After Sol's hash-gate receipt,
Luna may checkpoint only the R253 contract/admission/current-state records;
that administrative commit may advance branch HEAD without changing any
pinned source or reviewed artifact. The producer records both refs and exact
pin results; Luna reconciles the named commit contents before independent
review. Do not describe an administrative HEAD advance as source drift or as
a failed pinned-byte match.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` | `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7` |
| `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md` | `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf` |
| `tasks/agent-loop/inbox/20261019-r70-proof.md` | `25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db` |
| `tasks/agent-loop/inbox/20261019-r70-closeout.md` | `ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb` |
| `notes/progress/2026-10-19-r70-closeout.md` | `a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8` |
| `notes/theory/2026-11-02-ordinary-drain-progress-r250.md` | `87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574` |
| `tasks/agent-loop/inbox/ordinary-drain-progress-r250.md` | `8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65` |
| `notes/theory/2026-11-02-ordinary-birth-charge-r251.md` | `1bc35d4749290a6a583ce079e80a95ed96c60a9ff81db06e2dfac25e74ad2af5` |
| `tasks/agent-loop/inbox/ordinary-birth-charge-r251.md` | `8aaa7b025dd89e2f4edc0fb12ae69a9e1934ac7709c6bf719fae9a1e6c234429` |
| `tasks/agent-loop/sprints/ordinary-birth-charge-r251.md` | `30aea41a739866e73b6220754e05a8eb96388720046f87482714d530623cda23` |
| `notes/theory/2026-11-02-source-pair-credit-r252.md` | `057550871430512b1032ef166eed49f86661eb98150e462319978ffc36b19944` |
| `tasks/agent-loop/inbox/source-pair-credit-r252.md` | `f6c9c7918a9897be243654d7f6cfc681b1428b8c1d3da0714dcd605afeba84ea` |
| `tasks/agent-loop/history/20261102-r252-admission.md` | `af9e519531a9855cfd01b4bca2c709416bb4f1d4aa4bdcdd1eb5641749effd84` |

Verify every hash before citation. The R252 contract SHA-256 is `c54b7c3da6e93e358b410569d628369a4b7a6e51759e4015dd761fd65d7cd057`; its baseline movement is reconciled in the reviewed R252 history, so use the exact current R253 baseline above.
