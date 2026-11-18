# Independent review: finite alias observers and root trace

Reviewer: cycle262 pool worker; reviewed other authors' source, 2026-11-18 UTC.
No reviewed source file was edited.

## Scope and result

Read `GeneralFiniteAliasClosure262`, `GeneralFiniteAliasSearch262`,
`GeneralRebaseExecutableRequests262`, `GeneralRebaseExecutableSnapshot262`,
`GeneralRebaseRootTrace262`, and their actual Alias/Step/Runs definitions.
No correctness or claim-scope defect found in the reviewed versions.

Five modules were independently recompiled into a separate focused cache, in dependency
order, with `--trust=0 -DwarningAsError=true`. All exit0. Earlier dependencies were reused,
not rebuilt. This is an independent five-module rebuild, not a full repository build.
Exact SHA256 source versions and full output: `frontier-independent-build.txt`.
Reproduction: `python3 notes/verification/cycle262/rebuild-frontier-review.py`.

## Actual Alias equivalence

The target is exactly `GeneralNominalSaturationState.Alias`: reflexivity, edges from
the actual finite `state.aliases` list, symmetry and transitivity. It is not nominal
type equality, K2 inspection, packet validity or a hypothetical replacement relation.
Both procedures ignore state fields irrelevant to this relation.

The cut reference procedure includes root, target and both ends of every edge.
Soundness follows induction on actual Alias; completeness takes the filtered cut of
vertices related to root and proves it edge-closed. The classical predicate occurs
only in the proof of completeness, not the executable Boolean function. Its cut count
is exactly `2 ^ vertices.length`, including redundant cuts from duplicate vertices.
The reference is correctly documented as exponential, not efficient.

The frontier procedure starts visited at `[root]` and remaining at all edge endpoints.
`Covered` says every endpoint is either visited or remaining; it is initialized without
assumptions and preserved by moving the next frontier. A terminal unchanged remaining
list makes visited edge-closed. Alias induction then gives completeness for any query.
An isolated root is present from initialization, including when absent from every edge;
an unrelated identity absent from all edges cannot be manufactured by Alias. Intermediate
vertices absent from all sites remain available because endpoints come from all edges.

Self-loops and duplicate edges are handled. The lists need not be duplicate-free and
the code does not claim they are. Repeated identities may be appended to visited;
their later removal from remaining is simultaneous. Every actual recursive call uses
`rest != remaining`, and the filter-strict lemma proves strictly smaller list length.
The measure thus works with loops, duplicates, empty lists and initial overlap between
visited and remaining. It is a structural search termination proof, not a bound for
source-language execution.

## Request list equality

`requests_eq` is actual list equality. The implementation filters the original raw-sites
list by component membership, proves that predicate equal to the actual Alias predicate,
and uses the same flatMap of output lists. Consequently site order, repeated sites,
output order and repeated outputs are preserved. The algorithm does not reorder requests
using the traversal order of the computed component. One component is computed per root
in the definition; no asymptotic benchmark or end-to-end compiler performance is claimed.

## RootTrace state provenance

`Trace.next` retains root membership in `roots before`, the equation
`middle = write before (facts ... (requests source root))`, and strict progress at
that same before/middle pair. The remainder of the trace begins at exactly middle.
`from_runs` extracts these witnesses from actual proposal-list memberships, while
`to_runs` reconstructs a Step for every trace node. The sequence length is the actual
number of nontrivial writes, not a number of external observer calls or no-op scans.

`models_exact` proves the same trace/history for all assignments, rather than choosing
a history after seeing an assignment. It records effects conjunctively; repeated roots
do not introduce an incorrect distinctness assumption. The result preserves exact
source/root/plan effects, but source and plan remain fixed in this module.
`certificate` additionally gives actual settle success, progress budget and quiescence.
It deliberately does not conclude model existence, Ready, Good, Supported, packet
validity or general EvidenceNode. These omissions are accurately documented.

## Independent kernel probes

`FrontierReviewProbe.lean` contains ten successful kernel checks:

- empty edges, equal and unequal isolated identities;
- duplicate edges plus self-loops, forward and reverse reachability;
- disconnected components and an isolated external identity;
- a chain through a non-site middle identity and an absent target;
- exact component list showing retained duplicates;
- filtering an ordered repeated site-identity list preserves its order/duplicates.

The probes use the well-founded search equation with ordinary simplification, not native
evaluation. A first probe draft used `decide`, which cannot unfold this well-founded
recursive definition automatically; replacing that proof tactic with equation rewriting
resolved the proof elaboration issue without altering implementation or expected values.
All ten probes and ten selected axiom audits pass. Only standard propext, Classical.choice,
and Quot.sound occur. `frontier-independent-probe.txt` contains the final output.
No runtime benchmark, Yulang2 invocation or whole-repository build was performed.
