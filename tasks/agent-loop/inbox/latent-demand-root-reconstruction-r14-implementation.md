# LATENT-DEMAND-ROOT-RECONSTRUCTION/r14 — implementation handoff

Sprint / base contract: `LATENT-DEMAND-ROOT-RECONSTRUCTION/r14`, revision 2, SHA-256 `caf7474b5c34046bad8ff8599915dc2e1bc6d6aaf2cc28dbaff27509d9a06d91`.
Amendment ACK: R14 amendment 01, SHA-256 `b164d7e216715e9a89e2a09f78e863afc5536b76833bae58a50536545396b5cf`, authenticated against exact bytes; both implementation and proof lanes ACKed before the code edit.
Manifest: revision 2, SHA-256 `a07d873f38e1abf3be5eb86700d2942c156bff2f09a83dc62ec88f450ef0e395`; all 334 pins authenticated with zero mismatches.
Assignment-ID / handoff revision: `LATENT-DEMAND-ROOT-RECONSTRUCTION/r14-implementation`, revision 2 (successor to Luna-acknowledged rev1 SHA-256 `435edd9bce25ae13895c7d2771789613115465fe6ef40b1f56b9dd396401051e`).
Parent gate: `YulangClosure.SourceProblem.InferenceSoundness`; original source scope and quantifiers remain unchanged. Source/native Call/shared-witness, Generalize lawful-use allocation, effect hygiene, principality, termination and production remain OPEN.
Direct dependency basis: candidate baseline SHA-256 `0ca44b920d30e0a596584c9c4ad5e2a61fdd9115fe1eaaf4346ff64d0776afef`; proof/source handoff rev2 SHA-256 `b1e1253dbbb3ea918e8782619ba2a8bddfeba2842a2d84d80790eba0130ac17c`.
Role / worker / session: Luna/high implementer requested; `/root/latent_demand_root_reconstruction_r14_implementation`; observed model/effort and runtime launch receipt UNKNOWN. No descendants.
Exact leases: `isolated/latent-demand-root-reconstruction-r14/crates/yu-solver/src/candidate_scheme.rs` and this handoff only.
Outcome class: **provisional native implementation** of the bounded graph-local `M'` index relation. No source theorem, semantic repair or production promotion is claimed.

## End-to-end native behavior

The existing path starts at an actual Apply construction. `shadow_apply.rs:4130–4168` creates the negative Function demand with ordered Value/Effect/Effect/Value ports. For an authenticated formal omitted route, `DirectionalIntroduction` retains source registration and Call occurrence information; `candidate_context_seed` at Call slot 0 stores the demand root with `original_call`, `output_scope` and `input`. This metadata remains per relation/use; it does not consult or modify `formal_domains`.

Capture visits each captured bound relation. If its `ScopedFlow` contains a demand, `candidate_scheme.rs:2761–2787` calls `intern_shape(NegativeFunction(root), Negative)`. The same-graph endpoint interner canonicalizes the endpoint and returns its existing index or allocates a node slot and queues expansion. Capture drains queued expansion before publishing the graph; a negative Function node retains its ordered typed ports.

Publication still indexes the preexisting formal roots from `formal_domains`. The new bounded block then scans captured bounds with a relation and demand. For each demand it requires a negative Function term, the exact negative Function endpoint in that capture's still-live endpoint table, and a same-index graph node with negative Function polarity. It inserts that returned index into the existing graph-local root map; an existing key is accepted only if its index is identical. If the required endpoint/node is absent or inconsistent, publication returns `ReceiptMismatch`. It does not search by structural equality, synthesize an index, or skip a missing demand. `Graph::bytes` accounts for the map's retained capacity.

FreshUse remains the existing consumer: it remaps each relation's scopes/input, reads the retained root index, and uses the same reconstructed `terms[index]` DAG, updating `use_instance` only for local input. Evidence import still follows root reconstruction. Thus capture-to-FreshUse now retains the actual same-graph intern result for each demand root while preserving per-relation incidence.

## Consumers and unchanged permissions/guards

The root map now implements `M'_g = I_g restricted to (F_g ∪ D_g)`, where `I_g` is the actual endpoint-to-index relation from capture, `F_g` the existing formal composite roots, and `D_g` the demand roots attached to captured bound relations. Existing formal entries are left unchanged; equal demand roots in the same capture share only the one actual endpoint index.

All three consumers remain in place:

- `prepare_candidate_fresh_use` maps the root through that graph's `terms` vector and keeps the original bound relation's scoped data.
- `authenticate_demand_transport_observed` still checks matching route/use, original call and source relation, captured/imported evidence, scope/input remap, negative Function polarity, four ordered ports, FreshUse witness, physical fiber/readback and Replay ancestry (`candidate_scheme.rs:995 onward`). An index entry alone does not authenticate transport.
- `CandidateGraph::formal_effect_permissions` still begins with explicit `formal_permissions`, then requires the matching `formal_domains` entry and typed permission path (`shadow_apply.rs:2690–2723`). The new demand entries do not create permissions, formal domains, registrations or paths.

## Diff and evidence

Only `candidate_scheme.rs` changed under the source lease. The edit retains captured demand indexes at publication, checks negative Function shape/polarity, preserves equal formal entries, rejects conflicting/missing indexes with `ReceiptMismatch`, and performs no semantic changes elsewhere. Candidate SHA-256 at freeze: `f489868d88e6f56724bdd2c83d2979edc8a9a0c077dd4e81ff6c9f3ef374d4f0`.

Prior evidence reused: R13's independently reviewed Cargo-1 trace for invocation 1 / graph 3 / call 0, root Term 264 / node 11, bound 3 / relation 8, empty old map, and `ReceiptMismatch` before antecedent import. Its `EvidenceCoverage { gaps: 56 }` remains visible and supplies no antecedent eligibility. Static in-source tests were read as guard/identity context, not treated as executed checks. The proof/source lane's rev2 handoff supplies the candidate `M'` equation and complete field inventory, but explicitly does not establish source Call/Generalize adequacy.

Checks: none, as required by amendment and contract before fresh source-first review. Cargo, tests, build, Lean and static checkers were not run. No reviewer self-certification is claimed.

## Semantic boundary, budget and STOP

The amendment admits this representational candidate only. It does not establish that each native `ScopedDemand` denotes the same source-owned Call obligation under every lawful Generalize allocation, nor construct the existential source witness in `SourceProblem.InferenceSoundness`. Distinct independent uses still require their original scopes, inputs, providers, shared witnesses and event fields. No source domain, natural inference rule, guard, diagnostic, expected output or formal permission changed. No Simple-sub bypass was used. Parent/source-native, soundness, effect-hygiene, principality and production gates remain OPEN.

The existing 900-second assignment reservation was not reset. Exact launch timestamp, cumulative worker CPU/RSS and exact remaining seconds are UNKNOWN to this leaf; no executable/check process or background work was started. Requested lane Luna/high; observed model/effort UNKNOWN. No scratch/generated paths. Changed path set: candidate source plus this handoff. Both files are now frozen; writer state **STOPPED**, no descendants or unresolved descendant leases. Next step belongs to Luna: frozen source-first independent review; no Cargo before that review and Luna's acceptance.
