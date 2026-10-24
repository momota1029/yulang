# Lean root composition: checked conditional integration

LEAN-ROOT-20261024/r2. Baseline `61e509ae976aa1e0007fa76a5ff2f33e91362a11`. Original whole Yulang semantics/type-soundness/source-scoped A/B objective remains ACTIVE and OPEN. Compiler implementation is excluded. This milestone is a checked conditional composition and a connected obligation skeleton; it is not the concrete language instantiation or whole proof closure.

## Before/after evidence and original parent application

Before: no Lean project/toolchain entry was present in the worktree. The paper guide §3 assembled C informally. AH/RZ latest drafts were unreviewed, and AH2 lacked fixed-ambient/actual-parent anchoring across reassigned copies. The user's critique correctly identified that local lemmas were not closing the parent connections.

After: `Contracts.lean` gives separate machine steps, fixed-result typing, finite-cell simulation, certificate and one-step obligations. `CoreComposition.lean` proves `finite_prefix_composition`, `run_at_every_time`, and `saved_reusable`, and connects native success to the same-scope/source-witness elaboration using three explicitly supplied root obligations. All four exported theorem checks report no axiom dependencies. The same `Step` includes actual-resume premises against a current world; saved availability and admissibility are not manufactured by the theorem.

`SourceProblem` defines unproved elaboration, inference soundness, source-scoped coverage, principal coverage, native correspondence and inference termination propositions. These are parameterized schemas requiring the original source interpretation, not complete mechanizations of original A/B. `supported` includes the supported syntax domain, not only typable programs; principal existence is guarded by an actual original typing derivation. Qualification is mutual reachability within an immutable-birth induced graph. Defining it does not prove that a native pair has the requisite actual occurrence owner.

Exact next obligation: define corrected-core configurations, typing, all transitions and observations concretely; prove each `LocalLaws` field by the actual constructors, including both handler branches, No/rejoin, Fail, all seven frames and repeated current-world resume; connect each elaborated core judgment to actual initialization. Original source generation, shared scoped witnesses, publication/use, inference soundness/coverage/principality/termination, full surface and source/native correspondence still need their own evidence. No stronger arbitrary-assignment preservation requirement was introduced. No source case was removed to claim closure.

## Actual checking and repairs

Primary downloaded the official Lean4.35.0 Linux release into `/tmp/yulang-lean-root-20261024-czy6nl39`; no global configuration was changed. Release archive SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` matched the official asset metadata. Executed version: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Each module was checked in dependency order with `lean -j1 -M1024 -o …`. The first CoreComposition run failed because the generalized induction hypothesis required the initial invariant; primary repaired `(ih hc)` and rechecked successfully. Primary also corrected r1's principal-solution obligation on untypable inputs and added `native_success_elaborates`. These are coauthored changes, not independent review. A subsequent ordinary `lake build` completed exit0; its root audit output was:

```text
'YulangClosure.finite_prefix_composition' does not depend on any axioms
'YulangClosure.run_at_every_time' does not depend on any axioms
'YulangClosure.saved_reusable' does not depend on any axioms
'YulangClosure.SourceProblem.native_success_elaborates' does not depend on any axioms
```

These reports do not eliminate the theorem's explicit parameters/hypotheses. No `sorry`, `admit`, project axioms, unsafe proofs or native decision tactics occur in the three source modules. No compiler implementation or implementation tests were added/run. Generated proof build files stay ignored; the empty-dependency Lake manifest is retained. Proof checks used one verification owner, one CPU affinity for Lake, per-module `-j1 -M1024`,120sec command bounds. No Mathlib/downloaded project packages.

## Independent review and frozen receipts

Actual reviewer `/root/astra_semantics_review` returned FINAL/STOP: accepted as conditional composition; no BLOCKING or MAJOR findings. The reviewer checked all supplied frozen outputs and contract hashes, both Step cases, same result index/current-world distinction, explicit same-K availability, all-vertex birth filtering, source-scope/witness preservation and typable principal guard. It did not author the proof and did not rerun the checker; the execution receipts above are primary evidence. AH/RZ were excluded from the review and from proof dependencies.

Producer r1 frozen hashes before primary repairs:
- Contracts `c0113cfa24570377a68eb85efa0dd0c24fb31c9f3266dc8abe6c1d34c89397a5`.
- CoreComposition `2f8c1f16e87f43d818287805a1051f97b276bff7055a2f5ec5cf70fecc7e89e2`.
- README `da017a5636a534987e482c4e97343e66c7cd1e75cb6fe89836f131dfb7db6471`.

Reviewed README r2 SHA `5810662b4f2d56ccac03456af1d7afa5c452c019c4a999e2c06014da39058e8f`; subsequent changes are only acceptance status/receipt/link. All Lean mathematics and guide bytes are unchanged after review. Contract r1 SHA `7451ae9aabdd8efe26732903e0fc6a52b7975bcd6a3e7693175f47887dece0b9`; reviewed r2 SHA `52cab8f72182d8f5cc1f9501694b8e752d5897afd9ddaf9f5b36ff1f44e3fd34`.

| Integrated artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/README.md` | `cb174f9f17611c94f5d909bc06a4835995aa8b1feceb015607ea4cc677760821` |
| `notes/theory/lean/YulangClosure.lean` | `fdbcda98e4d8f9cbbff4280c0323cacb52d8f8fad928554a4b4f9f73e3c9faea` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/.gitignore` | `fde850d24186b6e99c8c0debd641fb3ab85198b109eb66f71a1fea02bd6ea1b3` |
| `docs/yulang-whole-proof-closure-ja.md` | `b2a42f8ad933f0456f184978db4b53177ab75ce0ad7c07ddac8427bd88c461f3` |
| `docs/yulang-proof-index-ja.md` | `4aa84bd4b6ffb2e9d01ebcb7b93c7af7b5de434fb51551c4ea3ef4f97777a466` |

## Resource, preservation and next boundary

Prior cumulative reservation9350 + direction30 + producer190 + reviewer80 =9650 seconds. This new method sprint used its full300-second envelope, max1 active child, three substantive stages; no automatic renewal. Full grants remain charged; observed active durations/model/effort UNKNOWN. Producer, direction and reviewer have actual STOP/FINAL receipts, no descendants. Primary alone owns integration; all generated/leased paths are accounted for. A subsequent material sprint must explicitly fix the concrete instantiation outcome rather than restart another local-lemma loop.

[Previous packet outcome](actual-copy-history-20261024-outcome.md) preserves AH/RZ as UNREVIEWED. AH r2 explicitly withdraws the insufficient AH2 application; it supplies no accepted theorem here. The original checkout and its unknown external leases remain quarantined. Withdrawn question files remain untracked and excluded. The previous snapshot is archived at `lean-root-20261024-prior-state.json`, not interpreted as current runtime evidence.

Static integration checks: eight frozen baseline/direct inputs matched; current JSON contract/history hashes and size checked; new document fences and exact new links/whitespace checked. Existing unrelated historical links were not certified. Intended Git scope is the two guides, Lean proof project, these sprint records, current state and the explicitly unreviewed preceding drafts. Whole original goal remains OPEN after this checkpoint.
