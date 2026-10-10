# Ordinary source reaches selected-owner Allowance restoration

Status: independently reviewed authentic-source characterization and
callback-local coverage for one restoration. Alternative A failure,
Alternative B impossibility, complete diagnostic rescue, and all-source
coverage remain open.

## Source and selected state

Baseline: `064f2af2b1a49df0b332b5980cfc5a105715c353` on
`research/simple-sub-intrusion`. The ordinary source keeps the established
selective-owner witness and replaces the final local `bridge` use with a
Function ascription in the defer initializer:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); my defer u = (bridge as ((int -> ['a] int) -> ['b] int) -> [
    E
    'q
] int); defer }
```

The inline spelling `[E, 'q]` was rejected by the parser before HIR. The
multiline row spelling above preserves the same annotation atoms and tail;
parser recoveries are empty. Normal `execute_candidate_graph_plan` returns
`Ok(())` with no solver errors. The ascription is in defer's level-2 local
scope; `'q` is distinct from bridge's `'t` and `'x` by source scope.
The experiment used the private candidate collector with the normal graph-plan
executor; it does not establish public/default concrete-formal admission.

At action 48, ordinary annotation checking installs the exact upper
`S53 − Allowance(8)` while S53 retains distinct old positive lower R47. The
new incidence is owned by source53/view8. At action 57, boundary-1 capture
includes the incoming bound while S53 and R47 are nongeneric and q96 is
generic. Freshening preserves S53/R47 and renames q96 to q113. This therefore
constructs, from real source, the previously unestablished unchanged-owner
restoration with a distinct old lower.

## Exact restore and callback coverage

At occurrence 27, S53 restores Allowance(9) at generation 8. The physical
opposite vector has saved `N=6`:

| index | physical opposite | canonical opposite | lower fiber |
| --- | --- | --- | --- |
| 0 | E47 | E47 | relation 186 |
| 1 | E60 | E53 | relation 253 |
| 2 | E47 | E47 | relation 186 |
| 3 | BottomPositive | BottomPositive | relation 187 |
| 4 | BottomPositive | BottomPositive | relation 187 |
| 5 | BottomPositive | BottomPositive | relation 187 |

The upper fiber is relation 515, with context 0. Before each indexed read and
before and after each callback drain, the owner, generation, saved count,
opposite vectors, and literal fiber heads remain unchanged. Each drain returns
`Ok(0)` with an empty worklist. The six callback children are
`[516, 515, 516, 517, 517, 517]`; each is emitted and dequeued. Thus this
restoration covers all six physical slots and all three unique ordered pairs:
`(186,515)`, `(253,515)`, and `(187,515)`. In particular, the child for the
distinct old lower R47 is present and dequeued.

Callback 1 appends a duplicate Allowance(9) to S53's negative upper vector.
It does not change the saved opposite vector or any input fiber, so it does not
shift or omit an old product in this execution. This corrects the earlier
candidate-specific constructor gap. It is not evidence that every callback
mutation preserves every old obligation.

## Review and evidence limits

An independent compiler-referee review passed both the source-to-state trace
and the callback-local observer. It confirmed the parser/HIR result, scope and
row identities, unchanged owner, distinct old lower, exact six-slot product,
child emission/dequeue, and the narrow scope of the claim.

The complete graph plan finishes after 92 further restores, 330 dequeues and
six merges. This one execution does not construct an absent or unrescued
child, a missing required omega, or an Alternative A failure. It does not
prove Alternative B impossibility, full diagnostic discharge, rollback/retry
completeness, or source/provider schedule independence. The selective
pre-merge SCC snapshot was not independently re-certified in this run. The
cached parser/HIR artifacts were byte-pinned, but their exact source build
provenance is unknown.

Evidence was produced in a private frozen-baseline copy. One standalone
compile and focused observer compile succeeded; an earlier observer compile
failed on a private-field access and was repaired in the private copy. Three
source executions completed, one prescribed inline spelling failed before
HIR, and one focused same-source callback run completed. The successful
callback run used one CPU, a 1.5 GiB address-space cap, and a 120-second
timeout; it took 0.316 seconds and peaked at 9,280 KiB RSS. No repository
compiler code, tests, or expectations were changed.

The next decisive premise is a source-owned callback mutation that changes the
restoring owner's opposite vector or ordered fiber heads before a saved index
is read, displacing a previously required pair without another actual replay
covering it. The observed upper-side duplicate does not do this. No
impossibility theorem has been established.

The full source, observer, logs, dependency manifests, and resource records
are retained under `/tmp/yulang-source-witness-search-20261011/`; the producer
report is `/tmp/yulang-source-witness-search-20261011.md`.
