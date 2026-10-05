# Finite SCC source-instance bridge: falsification boundary

Date: 2026-10-05
Status: frozen research artifact; unreviewed independent falsification attempt
Baseline: `a4cfe9babacd0a7094d25beeec73104613b74b95`
Lease: this file only
Method: mathematical premise sensitivity and separation of graph finiteness,
worklist termination, and size bounds; no source correspondence investigation

## Objective and claim class

Attack the conditional conclusion of
`2026-10-05-source-scc-instance-finiteness-bridge.md`, especially repeated
worklist evaluation. No counterexample to its stated finite structural graph
conclusion was found under all four premises. This is an analytical result
about the supplied hypotheses, not a search of accepted programs, a reviewed
theorem, or evidence that replacement source rules meet those hypotheses.

Two established mathematical observations below distinguish stronger claims
that do not follow: a finite canonical graph alone does not force an arbitrary
worklist driver to terminate, and the premises permit exponentially large
graphs relative to a linear-size abstract component/use inventory. Neither
observation contradicts the pinned note's actual conclusion. Their relevance
to source programs and implementation remains unverified.

## Governing baseline and dependencies

The frozen bridge's exact governing sections are Premises 1–4, Derivation,
and Scope boundary. Its local baseline is `757c90564`; this attack uses the
artifact as committed at the primary's pinned `a4cfe9bab` snapshot. Relevant
dependencies are the SCC foundation's Oracle invariant, Lightweight-port
boundary and Deferred semantic gates; charter §§3–4, 6; structural-theorem
§5; finite-context §§1–6; and the source-guard audit's Required source bridge
and conditional closure discussion.

Accepted authority is unchanged: F0–F2 infrastructure retains its declared
scope; the replacement charter and pure structural shadow confer no broader
source acceptance or implementation authority. No language meaning,
polymorphic-recursion policy, source limit, or publication rule is selected
here. The source-coverage question is outside this lease.

| Frozen input | Git blob at pinned baseline |
|---|---|
| `notes/progress/2026-10-05-source-scc-instance-finiteness-bridge.md` | `a1abc32ee7b5b9a536f2c5595c7df26b416ba426` |
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `4768a9869d4dd12861d292d71a56570102f370df` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | `658b106c18da450a2514c54496a12d840cd9d6c4` |
| `notes/progress/2026-10-03-source-guard-context-audit.md` | `9a54699c458d6e27bb3e9c5f806eb894cf7dab0a` |

All six blobs matched HEAD at the dependency check. Unrelated branch movement
does not change this frozen claim; subsequent dependency changes require the
primary to revalidate the affected premise.

## Premise sensitivity: where an infinite graph would have to enter

This attack does not reproduce the bridge's topological derivation. It asks
which permitted operation could supply infinitely many graph identities.

| Proposed growth route | Exact premise it violates |
|---|---|
| Infinitely many components or static use occurrences | Finite condensation DAG and finite source inventory |
| Freshly expand a self/internal scheme at each recursive reference | Premise 2: all such uses link to preallocated live member endpoints |
| Accumulate a fresh external copy on every worklist visit | Premise 3: one finite canonical instance per static use, with no visit-driven accumulation |
| Copy an infinite target graph or unfold its recursive edges during instantiation | Premise 3: target and instance finite, sharing/back-references preserved |
| Unfold a cyclic closed graph into an infinite published scheme | Premise 1: finite graph-preserving publication |
| Keep adding normalization, context, provenance, or replay identities | Premise 4: finite closure and canonical state/dependency-version space; no depth/iteration-driven identities |

These are abstract premise violations, not accepted-source counterexamples.
The final row is decisive: premise 4 already requires finite closure of every
finite component input. An infinite allocation witness that satisfies the
earlier premises would falsify that premise, rather than falsify the conditional
theorem. A source bridge must justify this requirement independently of the
finite-product argument; treating the required closure as a source rule would
leave the central obligation assumed.

## Smallest nonempty worklist witness

Consider one SCC containing one preallocated root `r` and one internal self
reference. Its closed graph is

```text
V = {r}
E = {(r,r)}
Q = [r]
visit(r): observe the existing self edge; add no graph fact; enqueue r
```

Publication is the identity graph projection. There are no external uses.
All generated endpoint, edge and dependency identities are fixed; premise 3
holds vacuously. The logical graph closure is already complete and finite.
The driver nevertheless has the transition

```text
(V,E,[r]) -> (V,E,[r]) -> (V,E,[r]) -> ...
```

This is the smallest nonempty vertex/work-item inventory supporting repeated
self-triggered evaluation. It shows that the four graph premises do not
exclude an infinitely running driver that requeues unchanged work. It is not
a witness against finite graph generation, nor a claim about a real solver's
behavior. If “closure” is read as requiring the actual driver to return, this
driver violates that reading of premise 4 instead; the termination conclusion
then depends on that additional operational premise.

Canonicalizing state identities, limiting dependency *values*, or making
evaluation fair does not by itself prohibit this no-change requeue. A separate
driver argument must bound processing events: for example, enqueue only on a
strict finite information increase, with finite initial work and finitely many
notifications per increase. This example proposes no implementation choice.
The finite-context dependency already states the stronger monotone/terminating
update premise in §3.7; its finite-state product must not be cited after
dropping that premise or read as a theorem about every possible scheduler.

## Finite graphs can still be large

For each finite `n >= 0`, take components `c_0,...,c_n`. Component `c_0`
contains one local root. Each later component has one local root and exactly
two distinct static external occurrences targeting its predecessor. Let each
use copy the whole predecessor scheme, preserve all sharing within that copy,
and give the two copies disjoint fresh endpoint identities. Publish each
whole component graph, with no unfolding or closure allocation. No component
has an internal use; closure is the identity operation.

Every premise is satisfied by this abstract family. The inventory has `n+1`
components and `2n` use occurrences. Its last scheme has size

```text
g_0 = 1
g_i = 1 + 2*g_(i-1)
g_i = 2^(i+1) - 1
```

The equality follows by substitution and induction on `i`. Every individual
graph is finite, but this family has no polynomial size bound in `n`. Finite
within-copy sharing does not require sharing between independent external
instances. This is a representation-level stress family allowed by the stated
premises, not a source acceptance witness, production lower bound, or demand
to share independent instances. A different publication/instance
representation could avoid this particular expansion; the theorem does not
choose one.

More generally, the bridge's `k(c)` is an existential finite closure size,
not a computable source-size bound or a bound on total solver work. No
practical resource envelope follows from that notation alone.

## Independence, coverage and stopping condition

No oracle or executable checker was used. These constructions share only the
pinned bridge's mathematical premises; they do not assume a separately
implemented transition system to validate source transitions. The worklist
transition is explicitly a hypothetical driver, and the copying family is an
abstract graph family. Their implications can be checked directly from the
definitions. This producer does not certify its own note as independently
reviewed.

Coverage: finite DAGs, cyclic internal roots, zero external uses in the
minimal scheduler witness, multiple independent external uses in the size
family, finite graph projection, finite closure, and repeat evaluation. The
mathematical size family covers every finite integer `n >= 0`; no enumeration
or random sampling was performed. Seeds/ranges for executable searches are
not applicable. The sensitivity table lists named premise mutations; none
was executed.

Omitted: source generation/correspondence, accepted program witnesses,
effect/handler/State rules, actual replay semantics, a scheduler algorithm,
computable closure bounds, and performance measurements. No completeness
claim is made for all possible attacks. Further equivalent finite toy probes
would leave the same premise untouched: actual rule-level finite closure and
operational update termination are not supplied by this mathematical attack.

Recommended next action: have the primary keep the finite-graph result
conditional and require the actual closure/worklist specification to identify
its finite canonical carrier and the progress argument for dependency updates
before using it as termination evidence.

## Checks, resources and frozen handoff

Read the three requested rule files. Read the bridge and pinned dependencies
from Git objects; the initial guessed bridge filename did not exist and was
resolved with a tree listing. One combined dependency read exceeded output
capture; the directly relevant missing charter §§3–4, 6, structural §5 and
finite-context §1 were subsequently read separately. No conclusion relies on
the uncaptured intervening text. Baseline/HEAD blob equality was checked with
`git rev-parse` for the six exact inputs above.

Budget: at most eight sequential lightweight tool operations, including the
leased write and final artifact inspection; no simultaneous shell operations.
Git reads inside Python were sequential. Shell-command wall times returned by
the tool were each below one second. Peak process memory, cumulative child
CPU, and model reasoning wall time were not measured. No builds, tests,
probes, benchmarks, compiler edits, Git mutations, or child agents occurred.
Final inspection checks only the leased artifact and pinned dependency blobs.
Writes stop before this artifact is submitted for review.

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-source-scc-finiteness-falsification.md`.
- Baseline SHA: `a4cfe9babacd0a7094d25beeec73104613b74b95`.
- Dependency hashes changed: none at the recorded check; hashes above.
- Claim/review status: frozen, unreviewed research; no all-premise graph
  counterexample found; scheduler and size separations only.
- Checks already run: pinned artifact/dependency reads, six baseline/HEAD blob
  comparisons, narrow leased-file inspection. No executable verification.
- Proposed commit message: `research: bound SCC finiteness falsification claims`.
- Shared-record deltas left for primary/curator: record this bounded attack
  and distinguish graph size finiteness from operational termination and
  practical resource bounds if adjudicated useful. Do not mark source
  coverage, the finite-context bridge, or inference replacement complete.
