# SCC copy, canonical closure, and late-update premise separation

Date: 2026-10-05
Status: frozen, unreviewed research checkpoint; abstract non-entailment witnesses
Baseline: `41fd79eafc51e23ee971f66af9951070851bb9ed`
Exclusive lease: this file only
Implementation authority: none

## Objective and governing inputs

Target only the missing finite scheme-copy/closure and late-update progress
premises. Method: minimize three abstract failure mechanisms and give a
conditional sufficient argument. No accepted-source counterexample, compiler
defect, replacement conformance, or independent review is claimed.

The primary supplied the baseline and confirmed that the three prior SCC notes
are committed and unchanged. Inputs were read from the filesystem without Git;
their captured hashes below let the primary verify baseline equality. The
current implementation bridge is read evidence, not implementation authority.
Its own older baseline is retained provenance, not this assignment's baseline.

Exact governing sections:

- `2026-10-05-source-scc-instance-finiteness-bridge.md`: **Premises** 1–4,
  **Derivation**, **Scope boundary**.
- `2026-10-05-source-scc-source-coverage-construction.md`: §§4–7, especially
  the missing publication/copy/replay clauses and existing independence witnesses.
- `2026-10-05-source-scc-finiteness-falsification.md`: **Premise sensitivity**,
  **Smallest nonempty worklist witness**, **Independence, coverage and stopping
  condition**. Its unchanged-work requeue and exponential-copy family are not
  repeated here.
- `2026-10-05-source-scc-current-bridge.md`: **Counting derivation** items 4–5
  and **Exact successor premise gap and next action**. Item 5 expressly requires
  well-founded constructor traversal after Recursive nodes become leaves.
- `2026-10-03-source-context-finite-closure.md`: §§2–3, especially uniformly
  bounded hyperedge arities, finite canonical carriers, and finite terminating
  dependency updates; §§4–6 delimit source coverage.
- Authoritative `2026-09-20-constraint-collection-scc-foundation-draft.md`:
  **Oracle invariant**, **Lightweight-port boundary**, **Phase and fact
  ownership**. F0–F2 excludes solve-discovered dependencies, occurrence values,
  scheme copying and publication. It requires a later approved owner before
  such dependencies are admitted; no published component may be reopened.
- Reviewed `2026-10-04-source-generated-callback-structural-theorems.md`:
  scope header and §5's finite monomorphic generator. It preallocates recursive
  binder endpoints; it supplies no general scheme/freshening semantics.

Accepted boundaries remain unchanged: the successor's source semantics and
polymorphic-recursion policy are not selected here; F0–F2's authority stays in
its declared scope. The three requested repository rules were read in full.

## 1. Finite cyclic scheme does not ensure structural copy returns

Take two abstract components with one static external use, so the source/use
inventory and condensation DAG are finite. Supply its provider with the finite
rooted scheme graph `V={r}`, `child(r)=r`, labelled by one unary constructor.
This is a finite graph, not its unfolded tree. Assume publication preserves it.

Consider an explicitly hypothetical copier with initially empty memo `M`:

```text
copy(v):
    if v in M: return M[v]
    children = [copy(w) for w in child(v)]
    result = construct(label(v), children)
    M[v] = result
    return result
```

The first call to `copy(r)` recurses to `copy(r)` before inserting any memo
entry. By induction on call depth, every active call sees `r` absent from `M`.
No call returns. One node and one self-edge are minimal among nonempty cyclic
child graphs; deleting that edge makes this particular obstruction disappear.
An acyclic finite child graph terminates by induction on its maximum child-path
length. A representation which terminates constructor traversal at separately
preallocated recursive references also removes this obstruction, conditional
on that invariant. Merely allocating finite binder rows does not prove it.

**Exact failed premise:** SCC bridge premise 3's operation must actually create
a finite instance preserving back-references. Its finite target-graph conjunct
holds here; a terminating copy operation has not been supplied. This also fails
the additional well-founded-child premise of current-bridge counting item 5.
It is not a counterexample satisfying all four SCC premises. No claim is made
that the hypothetical raw child cycle is constructible through current APIs.
Finite representation and successful finite traversal are separate obligations.

## 2. Finite states and labels do not ensure finite canonical hyperedges

Now make the provider scheme a single acyclic atom: its copy trivially returns,
and the one static occurrence keeps its canonical instance. Keep one canonical
comparison state `q`, one originating root, and one label `L`. Initially emit

```text
e_1 = (L, [q], [q]).
rule: e_n -> e_(n+1) = (L, [q repeated n+1 times], [q]).
```

Hyperedges are interned by their complete ordered parent/conclusion tuples.
Each rule application terminates and uses only existing endpoint/state/label
identities. Every `e_n` is canonical and finite; different lengths are different
keys. Induction gives `e_n` for every positive integer `n`, hence infinitely
many edges despite one state and one label. The key records its actual tuple,
not solver iteration, fresh names, or a nested path-expression label.

This is minimal in state/label count for a nonempty parent-bearing example.
Deleting the tuple-extension rule stops this witness. Imposing a finite parent
arity bound stops this specific growth. Whether duplicate parents may be
meaning-preservingly removed requires a separate rule-relevance argument; no
such canonicalization is selected here. Logically redundant conjunctions can
still have distinct representation keys if the canonicalizer retains tuples.

**Exact failed premises:** SCC bridge premise 4 explicitly requires finitely
many additional nodes **and edges**, which this violates. Finite-context §3
premise 2 requires uniformly bounded parent/conclusion arities, also violated.
Finitely many rule schemas and individually finite tuples do not establish
that uniform bound. If “finite labelled operands” in §3 premise 4 means the
whole tuple carrier, that condition fails as well. No claim is made that this
rule is an actual source or solver rule. Premises 1–3 can hold in this abstract
model; finite comparison-state count alone is the insufficient shortcut.

## 3. Finite monotone late updates can be missed

Use one canonical comparison state `q`, one existing dependency port `d`, and
two dependency values ordered `0 < 1`. No new SCC arc, endpoint, scheme copy,
or context is created. A correct abstract check should cache the current value
of `d`. The following hypothetical event order loses a notification:

```text
1. q reads d=0; its cached answer is not yet committed/subscribed.
2. d increases to 1; notify current subscribers, of which there are none.
3. q subscribes to d and commits the previously read answer 0.
4. the work queue is empty; the driver returns with q's stale answer 0.
```

This order is a serial abstract event trace; no concurrency mechanism is
assumed. The dependency changes exactly once, monotonically. The state/graph
and version sets are finite; replay, if invoked, uses the same `q`. Nevertheless
`q` is never rechecked against version 1. The process can terminate without
reaching exhaustive closure. This differs from an infinite unchanged requeue
or a two-value oscillation: the failure is a missed relevant update.

**Exact failed premise:** finite-context §3's **fair exhaustive closure** and
the relevant-change recheck requirement in premise 7's invalidation alternative
are absent. Finite monotone information supplies a finite change count, but
does not supply complete delivery or detection of those changes. SCC graph
premises 1–4 need not fail: their finite-graph conclusion can still hold for
this stale result. This witness attacks completeness/progress, not that graph
conclusion. Queue fairness among already enqueued items cannot repair an item
that was never enqueued.

Two values are minimal for a stale-version distinction, and one check plus one
dependency suffices. Remove the update and this failure disappears. Establishing
that subscription and observation cannot miss a change, or detecting the
version discrepancy before committing, removes this trace under its abstract
specification. Neither mechanism is authorized as a production change here.

Late updates to **dependency values within a supplied carrier** must be
distinguished from discovering a **new definition-dependency arc**. The latter
can change the SCC partition/order and is outside F0–F2 and the fixed-DAG
bridge's input. No reopening or incremental lifecycle policy is inferred from
the finite-update argument.

## 4. Conditional sufficient argument and precise remaining blocker

The following are candidate hypotheses, not established source properties:

1. Every incoming scheme is a finite graph; its copier visits each source node
   once using a cycle-safe identity map, or traverses a proved well-founded
   constructor relation with recursive references handled separately. Every
   individual traversal returns.
2. All closure states belong to a supplied finite carrier `Q`; all labels to
   finite `A`; the enabled rule identifiers form a finite set `R`, with common
   finite parent/conclusion arity bounds `p_max` and `c_max`. Interning
   preserves the distinctions required by the judgment.
3. Information increases strictly at most `h` times in a finite information
   order. Each state's initial admission schedules it; every relevant increase
   is delivered or detected. Each state receives at most one scheduling token
   per global increase, and processing a token terminates. Processing without
   an increase does not create another token for the same admitted state.

For finite labels, finite rule identifiers, and common arity bounds, the set
of canonical hyperedges is finite: it is contained in the finite union
`R x A x Q^p x Q^c` for `p <= p_max` and `c <= c_max`. Hypothesis 1 supplies
finite copying work for each of finitely many uses. With `K=|Q|`, hypothesis 3 bounds
tokens by `K*(1+h)` and makes every relevant final-version check reachable.
If processing is exhaustive over enabled finite rules, the finite queue drains
to closure. These counting arguments establish a conditional sufficient route,
not soundness, source-rule completeness, or actual implementation termination.

The precise blocker is an independently justified source/representation owner
for hypotheses 1–3: finite schemes alone do not prove traversal progress;
canonical state names alone do not bound tuple/edge closure; finite dependency
versions alone do not prove exhaustive rechecking. Another equivalent toy
checker would assume this same missing owner. Recommended next action: the
primary should assign one bounded correspondence audit of the selected
scheme/copy and closure/update clauses against these three obligations, retaining
an explicit blocker if those clauses are not yet specified.

## Independence, coverage, resources, and evidence boundary

No executable oracle, checker, mutation campaign, random seed, enumeration,
accepted-source fixture, test, build, benchmark, or Git command was used.
The witnesses have explicit hypothetical rules; their direct mathematical
consequences do not validate source transitions. Shared assumptions are only
finite inventories and the supplied conditional SCC premises. The current
bridge's implementation observations were not independently re-audited; this
note derives no compiler defect from them. Own inspection is not independent
review.

Coverage consists of three reduced abstract mechanisms. Section 2's induction
covers every positive integer tuple length, not a finite search range. Mutations
are analytical edge deletion, removal/bounding of tuple extension, and removal
or reliable detection of the one late update; none was executed. No exhaustive
classification or actual resource-performance bound is claimed. Effects,
handlers, guards, State, publication correctness, source admission, arbitrary
polymorphic instances, new late SCC arcs, rejection behavior, and semantic
soundness remain unverified.

Resource envelope: zero builds/tests/probes/heavyweight processes; no children,
Git operations, or shared-file writes. Eighteen lightweight shell invocations
total, including final leased-file/hash inspection, plus one leased apply_patch
write. The initial locator/rule batch issued five read commands concurrently;
subsequent commands were sequential. No compute search or process expansion
occurred. Reported command wait times were below one second each; CPU/RSS and
end-to-end reasoning wall time were not measured. Aggregate output capture
truncated two initial batches; required rules were fully available in individual
results, and the missed current-bridge counting passage was reread narrowly.
No conclusion relies on missing output. The lease was absent before creation.
The note is frozen after final inspection; future edits require a new handoff.

## Read-byte dependency snapshot

The primary owns comparison against integration HEAD. These SHA-256 values
describe the files actually read; this worker changed none of them.

| Path | SHA-256 |
|---|---|
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/progress/2026-10-05-source-scc-current-bridge.md` | `19668b2cd49b6f06c92b071538f73b31e03fc846abe39950b1f524f9418da213` |
| `notes/progress/2026-10-05-source-scc-instance-finiteness-bridge.md` | `8de7a8b07e8678be561c70bb127a6bd45586c65180c4b2ae6f0be655ad8d4eb6` |
| `notes/progress/2026-10-05-source-scc-source-coverage-construction.md` | `db586ac9ee7384c3f0ceb0b7ed715396f352b1da1f9e263109d8f831787e7eea` |
| `notes/progress/2026-10-05-source-scc-finiteness-falsification.md` | `cf2e211d5c52fac561961904cd5e2e55ea26ac9d971d845540b301efd931a592` |
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `37a2799288db0081cf3f32c7f6860c376ff0b2ce3249397cd9c23c7a89fedeaa` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | `dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-source-scc-copy-closure-falsification.md`.
- Baseline SHA: `41fd79eafc51e23ee971f66af9951070851bb9ed`.
- Changed dependency hashes: none by this worker; read-byte snapshot above;
  integration equality requires the primary's comparison.
- Review status: frozen, unreviewed abstract research; conditional sufficient
  argument and premise violations only; no all-premise falsifier or authority.
- Checks already run: exact rule/input reads, direct dependency SHA-256 capture,
  lease absence, final leased-file inspection/hash. No executable verification.
- Proposed one-line message: `research: separate SCC copy closure and late-update progress premises`.
- Shared-record deltas intentionally left for primary/curator: link this note
  if useful; retain the finite-SCC result as conditional; record traversal
  progress, bounded canonical hyperedge arity, and complete late-update
  notification as separate source-owner obligations. No task, theory, design,
  index, question-board, or production status was changed or promoted.
