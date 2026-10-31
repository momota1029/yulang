# R103 outcome

Status: `CLOSED_LEAN_FAILED_REVIEWED_RUST_UNINTEGRATED`; both R103 lanes are adjudicated under the fixed contract.

Contract: `tasks/agent-loop/sprints/effect-permission-capture-coherence-20261101-r103.md`.
Admission: `tasks/agent-loop/history/effect-permission-capture-coherence-20261101-r103-admission.md`.

No theorem, source/native, semantic, production, or Rust integration gate is closed by admission.

## Rust lane adjudication — review completed, no source integration

The Rust author stopped with the R102 focused Cargo allowance unused. Fresh independent compiler-referee review matched all frozen hashes and returned **REJECT for source integration**. The bounded invocation was described as safe but limited; I did not spend it because R103's missing-source-evidence stop condition applies and the fixed outcome cannot be established by this candidate.

The sole code change in this lane normalizes decimal `TermArenaBrand(...)` values in the memo observer comparison. Review accepts that scoped comparison repair: independently created `TermBuilder`s use fresh arena brands, while the test retains term indices and the rest of its selected debug structure. It has not been executed and does not prove full solver-state equivalence.

Four protected R102 failures remain unresolved: shared-tail error source/action identity; unequal `r != q` transport; consumer return/provider path; and positive Support lineage through fresh-use. The candidate leaves `candidate_scheme.rs` unchanged. Independent review also found `intern_shape` canonicalizes a raw endpoint before `intern` receives it, so the current observer may lose the raw origin and its witness precisely on an unequal transport. The test must not be weakened or the merge fabricated.

Review corrected two handoff claims: the shared-tail assertion follows the late `E` contribution and `constrain_live_effect`, so logs do not distinguish an earlier root error from rejection of that contribution; and a failed `.all(...)` proves at least one route lacks Support, not that every route does. The original r1 handoff remains frozen as reviewed evidence; these corrections and the exact next source owners belong in a successor packet.

No Cargo invocation, Rust integration, theorem closure, source/native correspondence, semantic approval, or production gate is claimed. The Lean proof lane remains active under R103.

## Lean pre-execution gate

Fresh independent `lean_prover` review: **PASS** for the frozen construction; this is not kernel acceptance. It verified all ten theorem headers against R93 modulo namespace, all original tree/forest constructors, App and four Lambda branches, full-route provenance, and one adjacent fully qualified `#check`/`#print axioms` pair per root. The reviewer independently reconstructed the flattened input. Its receipt is summarized here; reviewer STOPPED with zero writes/builds/checks/descendants.

Pinned environment was resolved read-only: Lake 5.0.0-src+eb6cafb and Lean 4.35.0, matching `lean-toolchain`; `lake env lean --version` also returned 4.35.0. No Lake build or dependency setup occurred. The existing Lean binary SHA-256 is `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

Primary authorization: exactly one `lean --stdin -j1 -M1024` invocation, with a 120-second timeout and one CPU, on the independently reviewed in-memory concatenation of `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, and R103; remove only the Generation→Syntax and R103→Generation leading import lines and add no separators. Frozen stdin is 111,624 bytes, SHA-256 `b0194148fb82d5a7c4b9af2bf8934764ec356cf2989b6cccd1cc9df1c69b7dcf`. Complete output and ten printed types/axiom lists will be preserved before independent receipt review. No cache, Lake build, retry, second invocation, or environment change is authorized. This gate covers the flattened ten-declaration candidate only; it does not establish module import integration, source semantic admission, the original A/B, native correspondence or production readiness.

Execution status at this authorization: **NOT RUN**.

## Lean execution result — reviewed failure, gate exhausted

The one authorized pinned invocation ran once and exited **1** (no timeout), elapsed **16.03 s**, peak RSS **901,016 KiB**, swaps 0. Exact command wrapper: `timeout -k 5s 120s taskset -c 0 /usr/bin/time -v /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`. The 111,624-byte reviewed stdin hash remains `b0194148fb82d5a7c4b9af2bf8934764ec356cf2989b6cccd1cc9df1c69b7dcf`; artifact hash `e31503875088a2f8dae68b1269433c4b9093a7d95e11ded03b7a169f56d6ecf0`; executable hash `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

Complete stdout: 15,703 bytes, SHA-256 `a33c8114f75e40687d7dcbd9755ac7a94bf4208ce2f174beed24b0875f3266dc`. Complete stderr/resource receipt: 864 bytes, SHA-256 `12e4a1797fa26678ede1e38abfdb310a8239f44cbcdffc00190e3bc585ff2f83`.

The same independent Lean reviewer returned **PASS for faithful failure receipt; REJECT for candidate acceptance**. It confirmed the exact hashes and counts and identified these errors: `appRule` still contains an underqualified `.roleAndInitialCallOrigin`; `app_exact` fails by `rfl` in both absent/present annotation branches. Eight roots have only accepted standard axioms, but `app_exact` and its dependent `app_inventory` each print `sorryAx`.

Complete transitive axiom results:

| Root | Printed axioms |
|---|---|
| `inventory_iff_lookup` | `propext, Quot.sound` |
| `encode_lookup` | `propext` |
| `observe_eq_follow` | `propext` |
| `source_membership_iff` | `propext, Classical.choice, Quot.sound` |
| `full_route_unique` | `propext, Classical.choice, Quot.sound` |
| `source_provenance` | `propext, Classical.choice, Quot.sound` |
| `app_exact` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `lambda_body_exact` | `propext, Classical.choice, Quot.sound` |
| `app_inventory` | `propext, sorryAx, Classical.choice, Quot.sound` |
| `lambda_body_inventory` | `propext, Classical.choice, Quot.sound` |

R103 Lean allowance is exhausted with no retry. Eight local results are useful but the ten-root candidate is not closed, not module-import-integrated, and not pushed as proof code. The first repair owner is the App rule helper/type and exact route equations under a new reviewed packet. Rust source also remains unintegrated per the independent R103 Rust review. Original A/B, source/native, semantic admission and production remain OPEN.
