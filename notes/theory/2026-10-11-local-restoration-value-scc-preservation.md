# Local fresh restoration preserves separation of Value extrusion parents

Date: 2026-10-11
Status: frozen research-only constructive source invariant derivation;
independent proof review pending. No parent rejection, soundness, principality,
or production gate is promoted.
Pinned compiler baseline: `74e027c9f8cbf37cb11acf4ce4a53b9613dbfedb`.
Live HEAD at initial re-pin: `587a2d5b523f2f33faf9224ed0348768e3711368`.
Exclusive lease: this note. Leaf only; static reads, no delegation or execution.

## 1. Frozen question, scope, and exclusions

The packet fixes the following statement, without an added source restriction:

> For every authentic successful `freshen_candidate_graph` /
> `route_candidate_local_run` / `begin_candidate_fresh_bound` sequence,
> immediately before an Effect child starts, no distinct retained Value
> extrusion parent/copy pair has become strongly connected since the last
> completed Value drain.

Here authentic means emitted by the existing source collection and native
candidate execution owners, starting from `try_new_candidate`, with the actual
captured order, sides, levels, parent records, and ordinary lexical/module
resolution. It does not mean an arbitrary graph assembled through test helpers.
Success is the existing fallible control flow; it does not assume semantic
consistency. Type-error continuation remains in scope. The statement includes
all supported current source forms, annotated and recursive locals, captured
older coordinates, interleaved restoration children, memo suppression, and
the later occurrence link. It does not assume every restored bound has a child.

All original source scopes, binders, occurrences, and causes remain fixed. The
parent proof's original dependent interpretation `xi = (nu,K,D)`, whole Call
witnesses, attachment/provider identities, and residual lineages are unchanged.
This lemma is about the actual dependency graph, not a replacement interpretation
of those semantic objects. No separately chosen port or marginal witness enters
the argument. No source annotation, early solving rule, rejection restriction,
new parent record, or compiler change is introduced.

Method: prove a numerical invariant at each actual Value-bound producer, then
exclude the first qualifying Value merge. The resulting statement is stronger
than the requested interval property: at this baseline's authentic native
source boundaries, no retained distinct Value extrusion parent/copy pair is in
one SCC at all. This stronger consequence concerns the current operation;
it is not an assertion that intrusion is dispensable or semantically correct.

Governing authority: Authoritative top-level inference principles §4 (and
§§1–3,5 for the proof/algorithm boundary); Authoritative parent-copy intrusion
“Selected operation and compiler responsibility”; compiler-engineering
“Natural compiler behavior and proof-obligation economy” and “Diagnostics
boundary”. The frozen parent proof §§4–5 and reachability audit §§3–6 supply
the exact unresolved premise, not proof of it.

## 2. Rank on the graph actually scanned by intrusion

Write `L(v)` for a live Value row's level. Define a structural ceiling `H(t)`:

- `H(ValueRow(v)) = L(v)`.
- `H(Function(a,ae,re,r)) = max(H(a),H(r))`, using the existing positive or
  negative endpoint view of the two Value ports. Nested Functions are traversed;
  row bounds are not traversed in this definition.
- Value leaves have ceiling zero. Levels are `u32`, so this choice is below
  every row level, including zero.

The Function construction DAG makes this definition finite. Both Effect ports
are retained by actual capture/reconstruction/comparison; omitting them from
this numeric measure does not remove them from Call or from inference.

The invariant for every physically installed Value bound, on either side, is

```text
H(item) <= L(owner).                                      (R)
```

`settle_candidate_intrusion` uses precisely the edges from a Value owner to
each lower/upper row or structural bound (`candidate_intrusion.rs:388–415`),
and from each Function to all four ports (`:449–472`). Hence (R) implies:
along any dependency path starting at a Value row and ending at a Value row,
the ending level is at most the starting level. For a structural bound this
follows by its two Value ports and induction through nested Function nodes.

An Effect path cannot return to Value: Effect rows have Effect endpoints,
and Support/Allowance has only an Effect tail (`:416–448,614–630`). Thus
crossing either Effect port cannot evade this inequality. This is a property
of the actual adjacency, independent of relation/context/protection meaning.

## 3. Initial state and the complete Value mutation owners

`try_new` constructs every Value bound row empty and every Value metadata entry
with `non_generic=false` (`lib.rs:10052–10100`). Source level initialization is
called there, before constraint admission (`:10103`; `candidate_source.rs:532–541`).
`try_new_candidate` then starts the candidate graph (`lib.rs:10136–10141`).
The bound invariant is initially vacuous and the extrusion-parent list empty.
`fresh_value_at_level` similarly appends an empty row at its supplied level,
with `non_generic=false` (`lib.rs:10156–10176`).

The production writes to `non_generic` are initialization, journal restoration,
and the OR transfer at parent/copy merge (`candidate_intrusion.rs:587–590`).
There is no production operation setting it true. Test-only mutation sites are
not source emissions. Thus it stays false throughout an authentic successful
native history. This is derived from the present owners, not a restriction
on the general Simple-sub concept of nongeneric variables.

The production Value-bound writer is
`candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:406–507`).
Its production callers exhaust the following cases:

1. `candidate_apply_value`, including replay-dispatched comparisons.
2. `candidate_extrude`: the one-sided source link and selected copied bounds.
3. `candidate_begin_bound_restoration`, through `begin_candidate_fresh_bound`.
4. `merge_candidate_rows`, for a qualifying Value parent/copy.

The `candidate_effect.rs` direct bound installations are Effect installations.
Source/annotation/operation/Apply/Lambda owners emit Value comparisons through
the ordinary native drain rather than writing Value bound vectors themselves.
The actual dispatch and candidate branches are essential here: `apply_value_task`
returns through `candidate_apply_value` before the legacy row-aging body
(`lib.rs:13744–13752`), and structural dispatch calls the legacy lowering
operation only when the candidate graph is disabled (`:12459–12481`). The
native graph path neither performs that legacy lowering nor adopts its
two-sided storage. No conclusion is drawn for an arbitrary mixed legacy/test
session or for future producers not in this dependency snapshot.

## 4. Preservation by application and real extrusion

### Row and structural comparison

`candidate_apply_value` selects the row with the greater level as physical
owner for a row/row comparison (`candidate_extrusion.rs:815–824`): if the upper
level is at most the lower level, it installs an upper bound on the lower;
otherwise it installs a lower bound on the upper. Both cases preserve (R).
Identical endpoints add nothing.

For a structural endpoint compared with a row, real dispatch first calls
`candidate_extrude` at that row's level (`lib.rs:12412–12456`). If the endpoint
changes, the original comparison is recorded with its rewritten child, and
the child is queued. It does not install the original unextruded structural
bound. The rewritten child passes through the same dispatch; if unchanged,
its structural ceiling is already at most the receiving row level, so
`candidate_apply_value` preserves (R). Atomic leaves satisfy it immediately.
Incompatibility and Bottom/Top shortcuts install no offending bound
(`lib.rs:12375–12410`).

### Extrusion output and copied-bound initialization

For a finite successful `candidate_extrude(t,p,T)`, every Value output has
ceiling at most `T`. This follows by induction on its actual work operations:

- A visited row with original level at most `T` is returned unchanged.
- A younger row receives a fresh copy at `T`; the memo is installed before
  bound traversal. Its endpoint therefore has ceiling `T`, including cycles
  through row bounds.
- A Function recursively uses the two reconstructed Value children, each
  with ceiling at most `T`, and also reconstructs its two Effect children.
  The output Function therefore has ceiling at most `T`.
- Value leaves remain leaves.

These cases are `candidate_extrusion.rs:73–156,216–255,325–355`.
Row memoization supplies the induction boundary for recursive bound graphs;
it is not an assumption of acyclic row dependencies. Structural nodes are
finished before deferred copied-bound installation. `Work::Bound` installs
the recursively returned endpoint on a copy at `T` (`:307–322`), preserving
(R). This proof applies to both polarities, including their flips on argument
ports and the selected side of row bounds.

The only authentic parent-retention constructor is the younger-row branch:

```text
L(original) > T;
copy := fresh_value_at_level(T);
retain_extrusion_parent(copy, original, p, T);
insert_bound(original, opposite(p), copy).
```

Owners: `candidate_extrusion.rs:83–124` and
`candidate_intrusion.rs:171–222`. Thus the real recorded pair starts with

```text
L(copy) = T < L(original).                               (P)
```

The source link is original→copy in intrusion adjacency, irrespective of its
semantic bound polarity, and preserves (R). Extrusion also constructs copies
for younger rows reachable through the selected bounds; the same argument
applies to each individually. Parent polarity/target are actual provenance,
not reverse dependency edges.

## 5. Capture and lexical use establish the restoration premise

### Captured Value bound ownership

Capture canonicalizes rows and classifies them by
`local = level > boundary && !non_generic` (`candidate_scheme.rs:300–326`).
`expand_row` returns immediately for a nonlocal row (`:569–570`). Every captured
Value bound is subsequently emitted from the expanded Value owner, preserving
its physical lower/upper side (`:572–621`). Context payload expansion introduces
Effect tails, not another source of Value-owned bounds (`:764–789`).

Consequently every captured Value-bound owner is local. Since authentic
metadata is false, every shared Value row in the graph has level at most
`B = graph.boundary`; every local Value row has level greater than `B`.
Shared rows' mutable bounds stay in the session and are not re-expanded into
the captured restoration stream. This conclusion covers older captured formal
parameters and annotation-created coordinates as well as ordinary components.

### The actual use level is at least the boundary

For module/incoming routes, `execute_candidate_graph_plan` publishes captures
at boundary zero (`candidate_scheme.rs:893–899`); incoming recapture retains
that boundary (`:952–960`). The use level is `u32`, so `U >= B` here, without
an extra inference premise.

For locals, the source scheduler starts at level one, preserves the level
through Apply, Group, Ascription and Lambda, and raises it only for a Block
initializer (`candidate_source.rs:251–287`). A binding is installed at its
containing Block's level `B`, with its initializer traversed at `B+1`
(`:288–326`). The Local action records the occurrence's actual traversal level
`U` (`:381–388`).

HIR lexical formation publishes a Local binding only within the surrounding
Block, resolves a Name from its active lexical stack, and restores that stack
when leaving the Block (`local_source.rs:366–373,396–437,637–647,819–829`).
Therefore a resolved published Local occurrence is in its containing Block or
a descendant; scheduler levels give `U >= B`. Initializer-only recursive
self uses take `Action::Link` on the open root (`candidate_source.rs:382–385`),
while later ordinary uses take Local freshening. Recursive/local annotation
publication retains the same containing boundary. This establishes the level
inequality from original lexical ownership; it does not add a naming rule or
limit the supported source domain.

### Fresh preparation and every restored Value insertion

Capture and fresh preparation are atomic at both incoming and Local entry.
`prepare_candidate_fresh_use` maps each local row to a fresh row at `U` and
preserves each shared row (`candidate_scheme.rs:1008–1021`), using one
canonical-row map to retain sharing. It reconstructs every Function with the
jointly remapped four ports (`:1118–1175`). It does not retain or erase
extrusion-parent records: its row allocation uses `fresh_value_at_level`,
and its other operations remap terms, Effect operands, contexts, bundles,
and captured evidence.

Every mapped Value row is now either fresh at `U` or shared at a level at most
`B <= U`; hence every reconstructed Value endpoint has ceiling at most `U`.
Every captured Value-bound owner is one of those fresh rows at `U`.
`begin_candidate_fresh_bound` retains the captured side and derives its owner
from the mapped lower/upper pair (`:1227–1247`). Thus its physical insertion
preserves (R), for every index and every side.

This reasoning does not require reordering bounds. `freshen_candidate_graph`
visits `graph.bounds` by increasing index (`:972–974`); the Local cursor uses
the identical index stream (`:1500–1514`). Actual capture order follows row
discovery and each owner's lower/upper lists, and may interleave Value and
Effect owners. Relation fibers, bundles, and antecedent evidence are transported
once before insertion (`:1248–1270`); their multiplicity changes replay children
but not the inequality just proved.

## 6. No first qualifying Value merge; ordered children and memos

Use induction on the authentic history up to a hypothetical **first** qualifying
Value parent/copy merge. Before it, Value representatives have not changed and
Value levels after initial setup have not changed: the only native production
Value level/representative update is that merge
(`candidate_intrusion.rs:585–593`). All other Value mutations above preserve
(R). Existing Effect merges may increment the generation and canonicalize
provenance, but update Effect rows/representatives, not Value levels or ports.

Each actual retained Value pair therefore still satisfies (P). Qualification
requires a path from copy to original in the actual dependency graph
(`candidate_intrusion.rs:476–491`). By (R) such a path implies
`L(original) <= L(copy)`, contradicting (P). There is no first qualifying
Value merge. This supplies the needed induction fact for the earlier steps:
fresh owners do not later redirect to a lower Value representative, and shared
Value levels and metadata do not unexpectedly change between captured indices.
The proof is not circular: it is preservation under all non-Value-merge
constructors followed by exclusion of the first Value merge.

The saved-count/restoration cases now follow directly:

- Physical insertion marks intrusion dirty and snapshots the opposite count
  (`candidate_extrusion.rs:668–677`). Even a zero-count insertion obeys (R).
  Its retirement without a drain (`:715–719`) consequently cannot create a
  qualifying Value SCC.
- For positive counts, the actual replay owner rereads the canonical owner at
  the saved index, keeps the orientation, and emits a task of the bound's kind
  (`:736–760`). Each Value child follows the preserving owners in §4; any
  parents it creates also satisfy (P). This includes all earlier children,
  not just parents present when capture began.
- Memo-current dispatch may suppress a Value pair before extrusion/application
  (`lib.rs:12349–12353`). That branch changes no bound or Value level. Reuse
  of a previously transformed structural child (`:12364–12374`) also preserves
  the invariant: original owner levels have not changed, and the child remains
  the actual previous extrusion result. No all-bound replay or diagnostic
  activation is assumed from storage alone.
- Effect restorations and children are sort-preserving. Context filters
  execute Effect bounds (`candidate_context.rs:2744–2803`), and Effect
  dispatch returns through the Effect apply owner (`lib.rs:12333–12347`).
  Intrusion may scan globally, but the first-merge contradiction still
  excludes every Value pair. Effect paths cannot close a reverse Value path.

Immediately before any actual Effect child starts
(`candidate_context.rs:3011–3034`), every retained distinct Value parent/copy
pair consequently remains in different SCCs. The requested “since the last
completed Value drain” conclusion follows; it also covers a prefix with no
earlier Value drain. Queue emptiness is merely its actual entry guard, not the
reason SCC separation holds.

Finally, the Local cursor admits its occurrence link only after all captured
restorations finish (`candidate_scheme.rs:1516–1519`). That link uses
`admit_candidate_value_link` and the ordinary Value drain (`:1338–1345`),
so §4 preserves (R) for it and for subsequent uses. Incoming publication also
links through its ordinary `route` after fresh restoration (`:1277–1300`).
A later Value link is not used to repair an earlier missed witness or justify
the pre-Effect boundary retroactively.

## 7. Exact consequence and remaining parent obligations

The audit's synthetic two-row discriminator contains the forbidden ascent:
after restoring `P` as a lower of `C`, it has `C→P` with `L(C)<L(P)`.
Its zero opposite count does not exclude that state, but the authentic Value
restoration construction above does. Alternatively remapping both generic
source rows to one fresh use level creates no parent record for those new
rows; copying a captured shape is not extrusion provenance. This explains
exactly why the synthetic state supplies no source counterexample here.

Applying this derivation to the reachability audit's conditional exclusion
removes its fresh-restoration entry premise **for the current native source
constructors**: an Effect child cannot induce a Value merge by that pending
zero-product route. The Effect diagnostics delta-clearing order remains an
actual consumer observation. This argument does not establish replay of all
preexisting persistent Value witnesses, every other error-detection route,
source inconsistency reflection, or the public export bridge.

The unexpectedly stronger absence of authentic Value parent/copy mergers is
an operational consequence to have independently attacked, especially against
the selected intrusion operation. It does not certify the complete inference
algorithm, assert that an intended source history can never need intrusion,
retire its correctness gate, or authorize removing/changing it. Future source
owners, a production operation that sets nongeneric metadata, or a native level
update would invalidate the corresponding owner proof and require fresh review.

Economy audit: the original rejection obligation remains class A and OPEN;
the local lemma is a constructional exclusion at its actual producer, not a
class change or a reconstruction relation. No third equivalent saved-queue
or synthetic-state proof is needed. The next decisive action is fresh independent
proof review of §§3–6 and their exhaustive native owner bridge. Complete Call,
effect hygiene, source Generalize, soundness, and required principality retain
their original scopes and OPEN status.

## 8. Evidence, limits, and frozen dependencies

Only bounded `rg`, `sed`, `cat`, read-only Git inspection, hash capture, and
this leased note write were performed. There were zero Cargo/build/test/probe/
Oracle/search processes, benchmark samples, Git mutations, or child launches.
One lightweight command process at a time; 45-minute wall limit. CPU/RAM peaks
and exact total wall time were not measured. Verification ownership remains
with the primary. Requested runtime: normal Sol/high proof leaf; observed
runtime model/effort metadata is unavailable, **unknown**. No Astra escalation.

All compiler dependencies read from the live tree were compared with the
pinned revision before use. The parent proof and reachability audit are
supplemental frozen notes added after the compiler baseline; neither is treated
as source authority or as already reviewed. Hashes and the final dependency
comparison follow. The final named dependency diff against the pinned revision
was empty for the eight compiler files, the two governing designs, and
`rules/compiler-engineering.md`. Static derivation is not
an executable run or independent certification.

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  notes/design/2026-10-10-parent-copy-scc-intrusion.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
12afc28af43c125960e072e2eac58df5fada65c3ce33b74aa61e1b66e2d8c1c9  notes/theory/2026-10-11-deterministic-rejection-proof.md
7c484507f96595ecd5388412e64d2016d0a8267dbb063447ebbc810e9c1bb925  notes/progress/2026-10-11-effect-drain-value-witness-reachability.md
```

Unverified: arbitrary injected states/test scripts, failed private state reused
without established invariants, future/new Value producers, the semantic
adequacy of the rank-preserving operation, full source rejection, persistent
witness coverage, publication/public consumers, complete Call and all
protection/attachment/residual interpretation, generalization/principality, and
production cutover. No code/assertion/test obligation is prescribed without
primary adjudication and independent review.

## Commit packet

- Exact leased changed path:
  `notes/theory/2026-10-11-local-restoration-value-scc-preservation.md`.
- Pinned baseline: `74e027c9f8cbf37cb11acf4ce4a53b9613dbfedb`;
  changed compiler/governing dependency hashes: none. The two supplemental
  proof/audit notes are absent from that baseline and pinned by their hashes
  above; this difference is explicit, not compiler source drift.
- Claim/review: constructive source invariant derivation, research-only,
  independent review pending; original rejection and principality parents OPEN.
- Checks already run: exhaustive static Value writer/level/metadata caller
  search, native-versus-legacy dispatch inspection, lexical scheduling/ownership
  inspection, direct dependency comparison, SHA-256 capture, and lease-scoped
  `git diff --no-index --check /dev/null <note>` (zero); no executable
  verification. Final artifact hash is returned separately.
- Proposed checkpoint message:
  `research: derive Value parent separation across local restoration`.
- Shared-record deltas left to primary/curator: record the rank/first-merge
  derivation as pending review, link it to the reachability audit's exact entry
  premise, and preserve all source rejection/semantic/public/Call/hygiene/
  generalization/principality gates OPEN. No shared record was edited.
