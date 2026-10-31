# LATENT-DEMAND-ROOT-VALIDATION/r15 — implementation handoff

Assignment: `LATENT-DEMAND-ROOT-VALIDATION/r15-implementation`; handoff revision **1** (frozen once). Contract SHA-256 `dc2e1a8a05052a573bff9d5341e2b11a0d937b84d56253e20ee1c07373e8c9ec`; input manifest SHA-256 `53464d82524e314e468bb02cf5ed49886a208be9bc2719d1da06ef242685ea32`.

Requested lane/model/effort: Luna/high. Observed runtime model and effort: **UNKNOWN** (not exposed to this leaf). Assignment reservation: 300 seconds; exact elapsed and remaining time **UNKNOWN** (no leaf timer/launch receipt exposed). No background work was started. Status: **STOPPED**, no descendants. This is a read-only producer handoff, pending fresh independent pre-run review and Luna adjudication. It does not authorize Cargo or claim self-certification.

## Exact snapshot authentication

- Contract bytes and manifest bytes match their assigned SHA-256 pins above.
- Manifest contains 426 entries: 418 `complete_cargo_workspace` files and 8 governing semantics/parent-theorem files. Every one of the 418 workspace files exists and matches its manifest SHA-256; no missing or changed workspace entry was found.
- Candidate `isolated/latent-demand-root-validation-r15/crates/yu-solver/src/candidate_scheme.rs` matches the approved immutable SHA-256 `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.
- R15 isolated root `Cargo.toml` and `Cargo.lock` byte hashes match R14's isolated counterparts exactly: respectively `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` and `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`. Both also match their R15 manifest pins. No package manifest or lockfile change was observed in this comparison.
- All 12 declared workspace members appear in the root manifest and have a member `Cargo.toml` in the snapshot.
- All 15 listed direct path references resolve on disk.
- Read-only `git ls-tree -r --name-only 31aa3451dff76185ccb642191f25e0dc97116342` comparison found all 94 tracked files under `apps/yulang-wasm`, `tools/bench-runner`, `tools/inference-playground`, and `tools/xtask` in the R15 snapshot; no tracked input is missing and no extra file under those four member paths was found.

## Native representation audit and prior evidence

The candidate preserves the narrow R14 construction. During capture, scoped demands on captured bounds are interned through the graph's endpoint table. Publication requires each demand root to be a negative Function, retrieves the actual endpoint index from that same capture, verifies the corresponding graph node and polarity, and retains that index in the existing graph-local `negative_formal_roots` map. An existing entry must have the same index; absent endpoints, wrong node shape, or conflicting indexes fail closed. `Graph::bytes` accounts for retained map capacity.

FreshUse uses the retained index to select the reconstructed term from the same `terms` vector, remaps the original scope/input, and assigns a fresh use identity only for local input. Root availability does not add a formal permission, formal-domain entry, source registration, or typed permission path. Existing transport authentication remains downstream and checks its route/use, source relation, evidence, scopes/inputs, ordered four Function ports, FreshUse witness, physical fiber/readback, and Replay ancestry. This is a static source audit; none of these checks were executed in this assignment.

Evidence reused:

- R13's independently reviewed Cargo trace established one finite same-invocation/same-graph observation: capture graph 3 interned root Term 264 at node 11; FreshUse reached bound ordinal 3/relation 8; the old map was empty and lookup failed before antecedent import. Its `EvidenceCoverage { gaps: 56 }` remains incomplete.
- R14 implementation handoff and independent review accepted only the generic same-graph index-retention representation. R14 Cargo failed while loading the workspace because `apps/yulang-wasm/Cargo.toml` was absent, so its fixture was not run.
- R14 source/proof handoff gives the native join and exact open source premise: show for each retained nondefault ScopedDemand and lawful source client allocation that capture/reconstruction preserves the source-owned Call at its translated telescope, with original provider/shared witness and fixed event fields, all four ports joined under one allocation, and no permission or antecedent authority inferred from index availability.

Evidence rejected for stronger conclusions: the R13 trace and R14 representation ACCEPT do not establish source Call/shared-witness adequacy, Generalize allocation, evidence eligibility or complete source/native correspondence. In-source assertions and this source inspection do not count as executed tests. No theorem, semantic repair, production readiness, or FreshUse test outcome is claimed. The static model's `map contains root` branch cannot establish that a compiled fixture reaches the next guard; only the separately authorized one-shot Cargo execution and retained logs could provide that bounded observation.

The R15 fixture is the unchanged `replay_constructor_lineage_observes_rejected_cross_route_authentication` in `candidate_scheme.rs`. Static assertions following `session.execute()` inspect completed restoration identity and fail-closed substitutions/removals, but remain unexecuted. The next concrete positive result, if independently accepted and produced under the separate Cargo grant, is limited to this candidate and fixture. Preserve the `gaps: 56` antecedent unless actual output establishes otherwise.

## Boundaries, checks, and freeze

Source `YulangClosure.SourceProblem.InferenceSoundness`, Call/shared-witness ownership, Generalize lawful-use allocation, complete source/native correspondence, effect hygiene, principality, termination, and production remain **OPEN**. No source domain, expectation, diagnostic, inference rule, guard, manifest or dependency was changed. No Simple-sub bypass is used or endorsed.

Checks performed: SHA-256 authentication; read-only Python 3 manifest/hash/path/member checks; read-only `git ls-tree` comparison; source and prior-evidence reads. No Cargo, tests, build, Lean, metadata command, Git mutation, or scratch file was created. The initial shell `python` lookup was unavailable (`command not found`); the audit used `python3` successfully. No disposable scratch/generated path exists from this assignment.

Exact changed path set: this handoff only. It is the sole authorized write lease. Handoff revision 1 is frozen after this write. Writer state **STOPPED**. No remaining work is assigned to this implementation leaf. A fresh reviewer should independently authenticate this receipt and the snapshot before Luna considers the single contracted Cargo attempt; source-law and parent theorem gates remain separate.
