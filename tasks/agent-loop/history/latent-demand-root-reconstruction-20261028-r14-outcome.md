# LATENT-DEMAND-ROOT-RECONSTRUCTION/r14 outcome

Status: **CLOSED_INCOMPLETE**. The bounded candidate received independent
source-first **ACCEPT** for native representation, but the contracted focused
fixture did not execute because Cargo could not load the isolated workspace.
No retry is authorized in R14.

## Frozen authority and evidence

- Contract revision 2: `caf7474b5c34046bad8ff8599915dc2e1bc6d6aaf2cc28dbaff27509d9a06d91`.
- Amendment 01: `b164d7e216715e9a89e2a09f78e863afc5536b76833bae58a50536545396b5cf`.
- Manifest revision 2: `a07d873f38e1abf3be5eb86700d2942c156bff2f09a83dc62ec88f450ef0e395`.
- Proof handoff revision 2: `b1e1253dbbb3ea918e8782619ba2a8bddfeba2842a2d84d80790eba0130ac17c`.
- Implementation handoff revision 2: `919451075e40c90a060fdd29473cbc228057e1b71eb4176e367fcc42911f29ce`.
- Candidate `isolated/latent-demand-root-reconstruction-r14/crates/yu-solver/src/candidate_scheme.rs`:
  `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.
- Independent review receipt: `tasks/agent-loop/inbox/latent-demand-root-reconstruction-r14-review.md`.

The only source change is the isolated `candidate_scheme.rs` generic retention
of actual same-graph interned indexes for captured demand roots, preserving
formal entries and failing closed on absent or conflicting indexes. Review
accepted that narrow representation. It did not establish source-scoped Call
or Generalize adequacy.

## Cargo-1 — manifest loading failure

The one authorized attempt used the exact contracted argv:

```text
cargo test --manifest-path isolated/latent-demand-root-reconstruction-r14/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

Environment: `CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target`.
Versions: Cargo `1.95.0 (f2d3ce0bd 2026-03-21)`; rustc
`1.95.0 (59807616e 2026-04-14)`. Start `2026-10-28T12:12:57.876656Z`, end
`2026-10-28T12:12:57.986761Z`, wall **0.1101 seconds**, exit **101**,
affinity **CPU 0**, sampled process-group CPU **0.0 seconds**, sampled peak
RSS **12,210,176 bytes**, no resource-limit termination. Stdout is empty.
Cargo failed while loading workspace member
`isolated/latent-demand-root-reconstruction-r14/apps/yulang-wasm` because its
`Cargo.toml` is absent. The focused test was **NOT_RUN**; compilation did not
start.

Retained logs under `isolated/latent-demand-root-reconstruction-r14/logs/`:

| File | SHA-256 |
| --- | --- |
| `r14-cargo-1.argv.json` | `60bbb422a3d6ded636e3e9c2c1eb238b98df39739b91e55c30425bacac424db4` |
| `r14-cargo-1.versions.json` | `8380e28dfb13417acace97d79857302eadcf20aba93766bd15bc300d886a78bf` |
| `r14-cargo-1.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `r14-cargo-1.stderr` | `767f83c21b4dd71a7259a4fbe18523221cc85414a13fa9e8a1b3ab44a574a963` |
| `r14-cargo-1.resources.json` | `b338393101f14906637871550415e6e77e49f1bd377f143410ab320e476f9091` |

This startup failure ends R14 checks. Cargo-2 was **NOT_RUN**. No workspace
repair, candidate revision, Lean execution or semantic patch was made.

## Remaining obligations and disposition

Source Call/Generalize adequacy, original `YulangClosure.SourceProblem.InferenceSoundness`,
source/native correspondence, effect hygiene, principality, termination and
production remain **OPEN**. Antecedent coverage gaps remain **56**; the native
map candidate does not establish eligibility or later FreshUse success.

R14 closes incomplete because its exact test witness could not be loaded from
the frozen isolated workspace. Any future check would require a new Luna
decision and exact versioned authority; it is not a continuation or retry of
this contract. No claim of semantic success follows from review acceptance.
