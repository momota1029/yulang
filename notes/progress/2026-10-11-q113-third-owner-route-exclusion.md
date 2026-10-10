# Fixed-source q113 third-owner transport route exclusion

Status: independently reviewed, conditional proof application for one exact
ordinary-source execution interval. It closes the proposed R47/R45 equality
transport route for this source; it does not close Alternative A/B.

## Statement and evidence

For the original frozen source at baseline
`064f2af2b1a49df0b332b5980cfc5a105715c353`, let the interval run from entry
through the sixth successful drain of the occurrence27 S53/Allowance9 restore.
The selected third-owner key is `(S53,+,R47)`, with R47 a negative copy of
R45. In this exact interval, no physical path `q113 ->* R45` exists at any
intermediate state. Hence the proposed cycle
`R45 -> R47 -> Allowance9 -> q113 ->* R45` cannot form, the 45/47 parent-copy
pair cannot qualify for merge by this route, and this route does not transport
the S53/R47 fiber before its selected product positions.

The derivation applies the previously reviewed successful-drain persistence
lemma to the six actual synchronous callbacks. Exact successful `Ok(0)`
drains, unchanged generation and representatives, and the reviewed boundary
closure of q113's two-node `{q113, Allowance9}` component exclude interior
merges and preserve any hypothetical intermediate path through each drain.
Between drains, the actual restore/replay owners only enumerate/queue relation
tasks; the initial selected insertion adds S53→Allowance9, not a q113
successor. Parent provenance and capture incidence are metadata, not physical
SCC edges. The original source log also shows the two scheduled `(186,515)`
products emit and dequeue child516.

The proof application is frozen at
[`prover route note`](/tmp/yulang-prover-r47-route-20261011.md). An independent
compiler-referee review rechecked all six frozen solver dependency hashes,
the observer/source evidence, edge orientation, graph writers, generation
argument, and interval boundaries: PASS, no findings.

## Limits and prover record

The result is conditional on the supplied authentic source/observer execution
and successful retained interval. It says nothing about semantic discharge
or diagnostic rescue and does not prove that another source constructor or
schedule cannot build the target state. A changed same-scope source which
restores a q105 return does so only after the six callbacks. Thus the requested
source-level A/B decision remains open.

The primary ran the configured `tools/codex-prover.sh` route. Its session JSONL
authenticates child `/root/prove_r47_route` with `agent_role=prover` and
`gpt-6.1-sol`; the prover's effective effort was not exposed. The separate
compiler-referee review was read-only. No build, source run, test, or
performance sample was added for this application. No production behavior
changed.
