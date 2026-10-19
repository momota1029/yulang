# R96 independent compiler/source review

Reviewer: fresh `compiler_referee`, independent and read-only; primary-preserved report.

**CLEAN for the frozen R96 finite source/candidate correspondence. No BLOCKING, major, or minor findings.**

The submission adds bounded observational evidence; it does not repair a compiler cause or change production behavior. That matches the contract.

Independent source inspection confirms:

- `local_source.rs:596–628,654–698,1236–1362` retains distinct original formals `t` and `d`, the helper’s own annotation, and `local_parameter_owners[d]=h`. Lexical lookup at `:1004–1044` resolves positive `pending` to `d`, negative captured `thunk` to `t`, and final `helper(thunk)` to `Local(h)` / `Parameter(t)`. Publish restores the initializer scope, preventing `d` from leaking.
- `local_source.rs:908–940` retains the adjacent call’s naked argument Name. Therefore `machine.rs:1478–1494` applies `direct_formal_root` to the genuine outer formal view.
- `candidate_source.rs:451–505,973–1044,1220–1257` visits both actual formals and scrutinees through ordinary candidate preparation. `program.rs:414–566` independently derives both Computation roles from their source annotations and preserves the exact Name identities. The proof correctly treats solve/no-conflicts and public runtime construction/start as execution seams.
- `machine.rs:879–1009,1858–1956` constructs distinct inert delays and receiving views. The helper closure retains captured `t→V_R`; helper entry binds `d→V_H`, whose image adds `bH` above inherited `bR`. Both Catch installations belong to helper invocation `uH`.
- `receiving.rs:230–323` supports the claimed contrast. Positive execution observes `V_H`, for which `uH` has an authentic receipt and reachable boundary `bH`. Negative execution genuinely reads `V_R` under `uH`, but its image contains only older `bR`. The unused entry receipt for `V_H` cannot match an observation of `V_R`. Matching family and endpoint cannot manufacture incidence.
- `machine.rs:1570–1684,1720–1728` supports the conditional shallow positive selection and negative `HandlerEvidence` boundary. View delimiters unwind while the helper owner remains live.
- `runtime_receiving.rs:158–167` changes exactly one Catch scrutinee through `replacen`, then executes both existing assertion helpers. Those helpers require successful parsing, candidate solve/no-conflicts, runtime construction/start, and the stated outcomes.
- R88 reuse is explicitly limited to unchanged grammar fragments. Its U/O/S whole-source bridge is not claimed for P/N. The proof preserves conditional, candidate-only boundaries and does not infer language rejection, native K,D, residual emptiness, general permission soundness, or semantic adoption.

Independently verified frozen SHA-256:

```text
contract       195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892
test           6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2
proof          2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9
proof handoff  84b3302c61e4a20e882552c960c95dadb5e9cb14bae80a5e9e810815f18de583
impl handoff   fb99947f978ab905bc65e5f7291ff38f18a74c062b2bc1fe2c5f85113f69b2d6
P, 210 bytes   765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780
N, 208 bytes   e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c
```

All inspected compiler/parser, governing authority, and R88/R92 dependency hashes match the proof’s frozen manifest. Handoff contents were not used as correctness evidence.

Limitations: read-only source review and in-memory byte calculation only; no writes, Git, builds, tests, compiler CLI, or descendants. The reported successful single test execution comes from Luna’s receipt, not reviewer execution. This review closes no semantic or general proof gate.
