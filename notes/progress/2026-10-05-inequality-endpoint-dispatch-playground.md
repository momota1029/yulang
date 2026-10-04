# Inequality endpoint-dispatch playground

Date: 2026-10-05
Status: bounded executable characterization; no complete-solver or production authority
Governing sources: [concrete compatibility boundary](../design/2026-10-03-concrete-compatibility-boundary.md) §1; [research-playground direction](../design/2026-10-04-inference-research-playgrounds.md)
Review: focused compiler_referee review; initial vacuous audit and reachability-evidence findings repaired. The latest lower/upper delta closed after adding the third user-approved optional-record edge and synchronizing counts; no remaining findings.

[`tools/research_inequality_endpoint_dispatch.py`](../../tools/research_inequality_endpoint_dispatch.py)
models the four endpoint shapes of the one `A <: B` query: variable-variable
edges, concrete-variable lower payloads, variable-concrete upper payloads,
and local concrete resolution. It exhausts all 512 directed edge graphs on
three variables and checks 13,824 edge-composition triples. An independent
adjacency-search oracle agrees with computed closure for all 512 graphs.
Concrete payloads never enter this graph.

The only concrete compatibility fragment is the already approved optional
record witness:

```text
{} <: {foo?: string}
{foo?: string} <: {}
{} <: {foo?: int}
{foo?: string} </: {foo?: int}
```

The script checks the endpoint dispatch matrix, shows that `X = Y = {}`
satisfies the two concrete-bound constraints around a variable edge, and then
separately resolves the direct concrete comparison as failing. It exhausts all
64 subsets of the six successful cells in this finite table to confirm the
model does not inject local evidence into variable-edge closure.

This exercises the distinction between transitive variable-bound propagation
and local concrete inequality resolution. It does not specify lower/upper
replay eligibility, general record rules, casts/adapters, solution
generalization, or a complete solver. Passing finite checks add no semantic
or implementation authority.

## Lower/upper payload interval witness (2026-10-05)

The checker now exhausts all nine `(lower, upper)` endpoint pairs in the same
three-record optional-field table, including all three directed comparisons
from the user-approved chain. Six concrete cells succeed, and all 64 subsets
of those cells remain outside variable-edge closure. Seven of the nine
lower/upper pairs have a concrete middle witness. For a variable `X`, it
retains `X` as the middle endpoint and enumerates concrete assignments
satisfying both direct queries `lower <: X` and `X <: upper`. Exactly one pair
has a witness while the direct concrete query `lower <: upper` fails:

```text
{foo?: string} <: X <: {foo?: int}
X = {}
```

A mutant that requires direct composition of the two endpoint checks therefore
rejects this nonempty interval. This repeats the approved nontransitivity
example as a variable-witness characterization and explicitly checks the
small finite assignment space. It does **not** define general lower/upper
replay eligibility, substitution, structural witness generation, or what a
complete inequality solver does when the finite concrete table has no middle
witness. It selects no new rule and is not a complete solver.

Verification: `python3 tools/research_inequality_endpoint_dispatch.py`,
`python3 -m py_compile tools/research_inequality_endpoint_dispatch.py`, and
`git diff --check` passed. A focused
compiler_referee review found one vacuous evidence loop and one reachability
claim gap; both were repaired, and the reviewer closed the delta with no
blocking or major findings. Search size and exact limits are the counts above.
