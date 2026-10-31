# R122 admission — computation-entry PRE-state

Sprint contract: `tasks/agent-loop/sprints/effect-permission-entry-prestate-20261102-r122.md`, SHA-256 `b0611e6bfaf5633887fcf566faeaeb5c7f29d7b8d68e6b09fece50fddb6cdcf7`.

Input manifest: `tasks/agent-loop/sprints/effect-permission-entry-prestate-20261102-r122-inputs-r1.json`, SHA-256 `9976ec1017181a8a5396db74b0ea4a03c6ccda31c272b24c831e136d1cc796d3`.

Admission baseline: branch `yulang3`, local and `origin/yulang3` at `f648047e17206665f986bea880ff89f0a90a3adf`. Exact immutable source/theory pins are in the manifest. The source lane and proof-application lane own disjoint handoffs only; neither can write compiler/theory source. No Cargo, test, compiler, environment or storage action is admitted.

## Live roster and capacity

Immediately before admission, `collaboration.list_agents` showed `/root` running and all listed children completed. The three newly UNKNOWN identities `/root/latent_demand_transport_classification_r17_source`, `/root/r80_proof`, `/root/r81_proof` were absent from the live roster. No child was RUNNING or WAITING, so no notification/acknowledgement was pending. The capacity-only refresh `tasks/agent-loop/history/20261102-capacity-release-refresh.md` (SHA-256 `906b5d6913d61440405d23796da10a9a721bd34291959e081858d3042f658e65`) covers the full 16 UNKNOWN identities, releases only reservation accounting, and preserves every UNKNOWN observation and path quarantine.

## Exact outputs and gates

- Researcher: `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-source.md` only; 300 seconds.
- Lean prover: `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-proof.md` only; 300 seconds; existing R39 theorem application, no new declaration.
- Fresh compiler referee only after both handoffs freeze; 180 seconds. Luna adjudication/closeout 300 seconds. Aggregate cap 1,200 seconds; Astra 0.

R111 verification-resource wait and all runtime quarantines remain unchanged. R122 may establish only the constructor's actual PRE-state premises or a bounded source obstruction; it cannot close R121's consumer indexed-read interpretation, provider arrival, subtraction, original A/B, whole-language effect hygiene/soundness or production.
