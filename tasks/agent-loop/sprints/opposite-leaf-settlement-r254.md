# Sprint R254 — source reachability of opposite-leaf survival after settlement

Status: ADMITTED under the unchanged full goal: Yulang inference soundness and its Rust implementation. Preserve original parent theorems, Simple-sub A/B, accepted source domain, quantifiers and semantics. Parent delta remains zero unless a justified result is applied at the unchanged original edge.

## Fixed outcome

R253 was independently reviewed PASS. NORMAL253/STORE253 excludes same-level birth through selected structural ports while both operands remain normalized. A genuine merge appends without recursively normalizing retained opposite structures. D253 names the remaining guard: a previously unselected opposite structural leaf must remain above the merged receiver after **all** qualifying/coactivated Parents settle, then survive representative transport and actual later replay/port/memo guards. R253 also established that one replay invocation cannot consume links born by its own queued children; later source-link waves require a distinct actual trigger. No accepted source witness or uniform multiplicity was shown.

Resolve D253 through complete Parent-closure analysis plus backward source slicing. At one concrete cutpoint retain the qualifying event/source identities, complete extrusion group and coactivations, both polarities' selected closures, pending order, opposite physical slot/fiber, raw and canonical representatives, and levels before/after the entire settlement suffix. Determine whether the exact opposite leaf is necessarily lowered; if not, backward-realize a particular accepted source prefix producing its survival. For a witness, continue through actual merged-lower replay, contexts, memo/rewrite and structural-port admission to a newly productive child. A surviving unused raw leaf without that consumer path does not qualify.

If the relevant slot comes from FreshUse/restoration, trace its actual `prepare_candidate_fresh_use` → canonical sharing/freshening guard → `begin_candidate_fresh_bound` → restoration path. This is targeted evidence for the chosen D253 path, not a global FreshUse theorem. Prove source-wide preservation applied to D253, or exhibit a source-qualified finite witness. A witness refutes that exclusion only; it does not establish Q253 wave unboundedness, divergence or a defect. If blocked, freeze the first new source-construction equation and owning producer/consumer. Keep R70 W, R71, evidence, diagnostics, Q253 later-trigger bounds, F1/FK1, foreign continuations and full soundness separate.

Implementation lane: Luna/high, **NO_SAFE_CODE_SLICE**. No production edit absent a concrete accepted-source violation of an approved clause.

## Assignment, leases, inputs and limits

One registered `prover`, Sol/high, worker `/root/sol_r254_opposite_leaf`, no descendants; maximum 2,400 active seconds across at most three substantive stages. Exact write leases:

- `notes/theory/2026-11-02-opposite-leaf-settlement-r254.md`
- `tasks/agent-loop/inbox/opposite-leaf-settlement-r254.md`

Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git.

Baseline HEAD: `b67a154ff7bedf23b937a915379f262ad71aaef7`.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
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
| `tasks/agent-loop/sprints/source-pair-credit-r252.md` | `c54b7c3da6e93e358b410569d628369a4b7a6e51759e4015dd761fd65d7cd057` |
| `notes/theory/2026-11-02-receiver-ancestry-renewal-r253.md` | `15458a226a3949e67b747540b1279dd054f1e280418c5746610bda4ce2933655` |
| `tasks/agent-loop/inbox/receiver-ancestry-renewal-r253.md` | `425b84efd46b590ecfddc69d24d7c75835be280cfaa7078fed66e5d0547eb680` |
| `tasks/agent-loop/history/20261102-r253-admission.md` | `f0ef140587ce60f7c54b534ddaaf26fd17276359d898cf829e4ef368b435d382` |
| `tasks/agent-loop/sprints/receiver-ancestry-renewal-r253.md` | `b5a6599eb29d3d451ca31ac621d9dd83cecfea162202ca0d9d0696d282b6e0d3` |

Revision 2 supplemental source-owner admission: the primary verified
`crates/yu-solver/src/shadow_apply.rs` SHA-256
`99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
before body reads. This is the actual Apply producer needed to connect
`candidate_source` actions to an upper Function and its checking relation.
No output, semantic, lease or budget changes. Contract revision 2 adds only
this exact read dependency.

Verify every hash before citation. R253's admitted baseline `901d1f9…` is reconciled in its reviewed history. Initial R254 baseline `b67a154ff7bedf23b937a915379f262ad71aaef7` was matched before body reads. The post-gate administrative ref `5bd27bbcd8a59250f59b68bf44fe3e05aa90d6d8` changes only R254 current/history/contract records; Luna verified the exact diff. Record this as administrative movement; source pins are unchanged. No further planned administrative HEAD movement before admitting any further new source owner.
