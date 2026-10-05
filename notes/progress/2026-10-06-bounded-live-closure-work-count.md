# Bounded work for one current live pair-closure drain

Date: 2026-10-06
Status: independently reviewed conditional current-implementation bound; one major premise finding repaired
Baseline supplied by primary: `2eac534be08798c2d9ce34f2f974b31ff610b374`
Repair/delta baseline supplied by primary: `3558688c9df9beb72dab569d04d4c831dce2887e`; original code dependencies unchanged
Scope: one current `InferenceSession::constrain_live` drain over supplied finite inventories
Method: constructive counting against inspected production transitions
Implementation authority: none

## Result and premises

The typed queue has a finite admission and enqueue bound. Duplicate enqueues
are allowed and are counted separately. A bound for all work inside the call
also needs a well-founded Function-child relation: extrusion marks rows but
does not mark Function endpoints. The validated existing-child construction
route supplies that premise for its immutable terms. Mere finiteness of an
arbitrary graph of supplied endpoints does not supply it.

This is a conditional theorem with the following explicit hypotheses:

1. During this call there are fixed finite, correctly polarized endpoint sets
   `V+`, `V-`, `E+`, `E-`. The initial `LiveConstraintTask` has its lower and
   upper endpoints in `V+` and `V-`, respectively, for a value task, or in
   `E+` and `E-`, respectively, for an effect task. These same inventories
   contain every endpoint retained in the initial bounds and every endpoint
   reachable through retained bounds and Function-child translation, including
   translation between value and effect sorts and the corresponding polarity.
   All referenced row ordinals and term handles are valid in the supplied
   session branch.
2. The initial typed queue is empty, as asserted at `lib.rs:11065`. The initial
   physical bound vectors are finite. Their multiplicities are included in
   the general formula below; endpoint cardinality alone does not bound
   arbitrary preloaded vector multiplicity.
3. No reentrant mutation or rollback changes the inventories, admitted memo,
   or bounds during the drain. Once admitted, a pair remains in `typed_pairs`
   throughout this call. The inspected loop has no removal transition.
4. Function-to-Function child edges form a DAG. Let `h` be the maximum number
   of Function nodes on a constructor-only path, stopping at rows and atoms.
   Validated immutable existing-child construction is sufficient for this
   hypothesis; arbitrary manually supplied cyclic graphs are excluded.
5. The call starts from the normal diagnostic boundary: old value memo entries
   are complete. Standard finite collection operations, reservations,
   accounting and journal helpers either finish or return an error. Logical
   counts use mathematical integers; successful machine execution additionally
   requires representable counters and successful reservations.

The supplied inventories are inputs to the theorem. This note does not bound
their size by source size, prove arbitrary session initialization invariants,
or authorize a production resource limit. It does not reinterpret language
meaning or establish successor/source/context rules.

## Exact inspected owners

All solver locations below refer to `crates/yu-solver/src/lib.rs`.

| Owner | Relevant transition |
| --- | --- |
| `ValueEndpointKey`, `CanonicalValuePairKey`, `TypedPairKey`, `LiveConstraintTask` (`:695`, `:717`, `:731`, `:3722`) | Fixed binary pair identity; diagnostic adjacency is outside identity. |
| `value_endpoint`, `effect_endpoint` (`:10599`, `:10631`) | Translate existing terms to atoms, fixed live rows, or existing Function handles. |
| `constrain_live` (`:11059`) | Pop; skip an existing memo key; otherwise admit once and apply or decompose. Function comparison emits exactly four typed children. |
| `record_typed_pair_admission` (`:11279`) | Insert with an assertion that the key was absent; add each new value key to one diagnostic delta. |
| `apply_value_task` (`:12071`) | Row edge installs two physical directional entries; membership installs one entry; replay enumerates retained opposite memberships/adjacency. |
| `apply_effect_task` (`:10853`) | Same edge/membership replay pattern for the effect sort. |
| `enqueue_task`, `enqueue_front` (`:11230`, `:11245`) | Append an item without checking its memo key; duplicates remain physical work. |
| `extrude` (`:10673`) | Visit each lowered row at most once per generation; Function endpoints emit four children without Function marks. |
| `record_diagnostic_edge`, `complete_diagnostic_delta` (`:11378`, `:11474`) | Retain value-child edges; finish the finite delta with SCC traversal and first-arrival witness settling. |

`crates/yu-solver/src/term.rs:1122,1142,1170` validate that Function children
already exist with the required kind/polarity before interning. `intern`
(`:1058`) returns an existing equal node or appends a new immutable node;
`push` (`:975`) and `TermPage::push` (`:1322`) publish a new slot. Along this
validated route, constructor edges go to earlier publications. Row-bound
cycles remain possible and do not invalidate constructor acyclicity.

The direct dependency
`2026-10-06-current-scc-copy-closure-correspondence.md`, sections 2 and 3,
already distinguishes this carrier/replay mechanism from successor closure.
This note adds a conditional work count without extending that correspondence.
Governing policy is `rules/research-lab.md`, “One semantic baseline,” “Writes,
artifacts and review snapshots,” and “Evidence quality”; `rules/design-authority.md`,
“Authority order” and “Approval and implementation gate”; and
`rules/git-concurrency.md`, “Disjoint-file mode” and the research checkpoint path.

## Carrier and persistent additions

Let `n` be the number of value rows, `m` the number of effect rows, `p` and `q`
the numbers of non-row positive/negative value endpoints. Let `f+ <= p` and
`f- <= q` count their Function endpoints. Effects currently have one non-row
endpoint on each side: positive Bottom and negative Empty. Thus:

```
Kv = (n + p)(n + q)
Ke = (m + 1)^2
K  = Kv + Ke
```

There are at most `K` distinct correctly polarized typed keys. If `a0` of
these keys are already in the memo, new admissions `A <= K - a0`. Counting
all possible keys is deliberately conservative: incompatible value shapes,
positive Bottom and negative Top can terminate before applying a bound task.

Hypothesis 1 supplies the base of the endpoint-inventory induction: the one
initial task is in the corresponding polarized product. Each admitted task
retains only its existing endpoints, and bound replay reads endpoints from
the same closed inventories. Function decomposition translates children into
those inventories with the required sort and polarity. Induction over queue
emissions therefore keeps every queued and admitted key inside the carrier
counted by `K`. The empty initial queue and one initial task give the `1` seed
in `Q` below; the induction bounds the admitted emitters by the row/membership
and Function-pair counts used there. No count or formula changes are needed.

At most `n^2` new logical value row edges, `np` new lower memberships and
`nq` new upper memberships are installed. These occupy at most
`2n^2 + n(p+q)` added vector slots. Effect additions occupy at most
`2m^2 + 2m` slots. An edge and its two directional slots are different counts.
Each addition is charged to its unique admitted pair; raw vector `push` has
no independent uniqueness check. The returned `transitions` count is another
quantity: it counts first `has_int_positive_lower` changes, hence is at most
`n` on a successful drain; it is not an admission or pop count.

## Enqueues with arbitrary finite initial multiplicities

For value rows let `L0`, `U0`, `Dl0`, `Du0` be maxima of initial lower
membership, upper membership, direct-lower and direct-upper vector lengths.
Use zero when there are no rows. At every point in this call:

```
L = L0 + p; U = U0 + q; Dl = Dl0 + n; Du = Du0 + n.
```

Define analogous effect maxima `Le0`, `Ue0`, `Dle0`, `Due0`, and put
`Le=Le0+1`, `Ue=Ue0+1`, `Dle=Dle0+m`, `Due=Due0+m`.
The following bound counts every replay emission, including duplicate keys:

```
Rv = n^2(L+U) + np(U+Du) + nq(L+Dl)
Re = m^2(Le+Ue) + m(Ue+Due) + m(Le+Dle)
Q  = 1 + Rv + Re + 4 f+ f-
```

The row/row task scans the lower row's lower memberships and upper row's
upper memberships. A lower membership scans opposite upper memberships and
direct uppers; an upper membership scans opposite lowers and direct lowers.
The same three cases give `Re`. A Function pair emits four children once.
All other tasks emit none. Every emitter has already been admitted and can
never emit again in this call. Therefore total successful queue pushes are
at most `Q`; total queue pops equal pushes on successful drainage, and are
at most `Q` on an error prefix. The queue's maximum live length is at most
`Q`. New semantic pair processing occurs at most `A` times; duplicate pops
perform no replay. This establishes the queue bound without assuming that
enqueue itself deduplicates or that queued work is bounded by `K`.

## Sharper bound under an explicit initial uniqueness invariant

If initially each directional row/membership vector has at most one entry per
corresponding canonical pair, and any initially installed pair is already
memoized, no later admission repeats an installed entry. Then total lengths
satisfy `L<=p`, `U<=q`, `Dl,Du<=n` and their effect analogues are `1,1,m,m`.
The resulting bound is:

```
Rv <= 2 n^2(p+q) + 2 npq
Re <= 4 m^2 + 2 m
Q  <= 1 + 2 n^2(p+q) + 2 npq + 4 f+ f- + 4 m^2 + 2 m
Bv <= 2 n^2 + n(p+q)
Be <= 2 m^2 + 2 m
```

This sharper statement is conditional on the initial invariant. The inspected
apply routines and memo driver preserve it, but a repository-wide proof that
every initial state enters through those routines is outside the leased read
scope. The general multiplicity-aware formula does not need that assertion.

## Extrusion and diagnostic work inside the drain

Let `Bv0`, `Be0` be total initial physical bound slots. Define final-slot caps
`Bv=Bv0+2n^2+n(p+q)` and `Be=Be0+2m^2+2m` for the general case.
In one extrusion, each row expands at most once, so at most `Bv+Be` bound
slots emit traversal roots. Removing row expansion leaves constructor trees
of height at most `h` and branching at most four. A deliberately coarse cap is

```
T(h) = 1 + 4 + ... + 4^h = (4^(h+1) - 1)/3
one extrusion's endpoint pops <= (1+Bv+Be) T(h)
number of extrusion calls X <= 2n^2+n(p+q)+2m^2+2m
all extrusion endpoint pops <= X(1+Bv+Be) T(h).
```

Function sharing can cause repeated constructor traversal, so this is not a
linear bound in distinct terms. Generation wrap may additionally clear the
`n+m` row-mark slots per extrusion. No new term or live row is constructed by
these transitions. Validity/finite inventory and constructor height are the
essential premises; monotonically decreasing levels alone would not prevent
a constructor-only cycle.

New diagnostic value edges `D <= Rv + 2f+f-`: each value replay adds one edge,
and a Function pair adds its two value children. Let `d<=Kv` be the new value
delta size. The inspected completion routine traverses finite delta adjacency,
forms SCCs, processes each SCC once, settles each node at most once, and
expands each internal reverse edge at most once. Direct seeds plus external
edge seeds plus internal expansions produce at most `d+D` candidate inserts;
discarded over-distance candidates only reduce that number. Bucket iteration
has at most `45d` slots summed over SCCs. Diagnostic edges may have duplicate
children and remain included in `D`. This is a bound on these logical events,
not allocator bytes, hash-map cost, helper accounting cost or measured time.
Witness distance or capacity overflow returns availability failure; successful
completion and panic-free invalid-input behavior are separate obligations.

## Minimal excluded witness and limits

A finite immutable graph containing one positive Function whose result child
is itself would make extrusion repeat that Function forever. Constraining it
below one row reaches extrusion before pair admission. Its remaining argument
and two effect children can be ordinary correctly polarized atoms. This is a
minimal conceptual Function-cycle witness to the inadequacy of *finiteness
alone*, not a constructible production counterexample: the existing-child
validation cannot publish that self reference. It was not executed.

Arbitrary duplicated initial vectors also refute a cardinality-only uniform
replay bound: one membership insertion can scan arbitrarily many copies of
the same opposite endpoint. They do not refute the multiplicity-aware formula.

No executable oracle was used. Evidence is source-grounded counting, sharing
the stated inventory and session premises with the implementation. No toy
checker is presented as proof of source rules. Seeds/ranges and mutations are
not applicable; no enumeration, probe, test or build was run. Source-size
expansion, schemes/freshening, arbitrary caches, later invalidation, successor
judgments, supported-input performance limits and allocator measurements are
unverified. Invalid row/term handles, constructor cycles, memo removal or
out-of-inventory mutation break the stated premises.

## Checks, resources and handoff

Review/finding history: an independent compiler_referee identified a major
gap in the original derivation: finite inventories closed under bounds and
children did not explicitly include the initial task's endpoints. This repair
adds that root-membership premise, makes reachable-bound/child closure in the
same inventories explicit, and supplies the base/step induction for the `1`,
`K`, and emission counts. Independent delta review passed: the premise and
induction close the finding, no formula changes are needed, and no new findings
were raised. The review covered the repaired premise, induction, and adjacent
carrier/queue claims; the prior complete formula/source review carries forward.
All other claims and formulas are preserved.

Repair checks: read this exact leased artifact, inspect the narrow textual
repair, and recalculate its SHA-256 at freeze. No production dependencies were
reread or changed in this repair; the primary reports the code dependencies
unchanged at the repair/delta baseline. The repair uses lightweight sequential file operations;
CPU/RSS and end-to-end wall time are unmeasured. No tests/builds/probes/Git or
shared-record edits were performed.

Checks run: bounded `sed`/`rg` source inspection, full reads of the three
required rules and the correspondence dependency, and `sha256sum` of direct
dependencies. No Git command, compiler edit, test, build, probe, child agent,
shared-record write or generated output was used. Local source-reading
processes were lightweight, with at most three concurrent readers; CPU/RAM
and total wall time were not instrumented. No numeric compute budget was
provided; this derivation used no compute wave or timed measurement.

Observed direct dependency SHA-256 values:

```
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611  crates/yu-solver/src/term.rs
42cbeeed9d9b99678df840831f1f6a84ac558fba3e831bfd33cce368514aff92  notes/progress/2026-10-06-current-scc-copy-closure-correspondence.md
```

Recommended next action: independently delta-review the repaired root-inventory
premise and its induction against the frozen major finding before accepting
this as current production work characterization. The primary owns baseline/hash validation
and any promotion into shared theory/task records. This note is frozen for
that review and makes no independent-review or gate-completion claim.

Commit packet:

- Exact leased path: `notes/progress/2026-10-06-bounded-live-closure-work-count.md`.
- Baseline: `2eac534be08798c2d9ce34f2f974b31ff610b374`, supplied by primary;
  not rechecked through Git under the no-Git assignment.
- Repair/delta baseline: `3558688c9df9beb72dab569d04d4c831dce2887e`, supplied
  by primary; original production dependencies reported unchanged.
- Dependency changes: none authored; hashes above identify observed inputs.
  Comparison to the pinned revision remains primary-owned.
- Claim/review status: conditional source derivation; frozen and independently
  reviewed after repair of the initial-root-inventory finding; no implementation
  authority.
- Checks already run: focused source/rule reads and dependency SHA-256 capture;
  zero tests/builds/probes.
- Proposed message: `research: derive finite current live closure work bounds`.
- Repair message: `research: require initial live-task endpoints in bounded closure inventories`.
- Shared-record deltas left for primary/curator: record the conditional queue
  and extrusion bounds, the constructor-DAG premise and initial-multiplicity
  distinction after adjudication; no successor closure or practical limit
  status promotion.
