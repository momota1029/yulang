# Recursive incoming member use: level reachability falsification attempt

Date: 2026-10-06
Status: frozen, independently reviewed research-only static characterization and conditional invariant derivation
Independent review: compiler_referee found no BLOCKING, major, or minor findings in the coupled level-invariant component; law (L) remains open.
Assigned baseline: `62560fbbc2d69971a80afec95fd34858c763024b`
Exclusive lease: this file only
Method: adversarial owner-ordered trace construction; no executable probe
Implementation and semantic authority: none

## Objective and outcome

Try to construct a legal production-owner trace in which the guarded extrusion
of the exact incoming occurrence row misses a younger row behind an already
aged row, thereby changing or failing to preserve source permissions in (L).
The supplied arbitrary-inventory example is not repeated as a counterexample.

No such owner trace was found. More strongly, an inductive installed-inventory
invariant excludes that syntactic shape for successful pure owner traces from
empty rows. Actual collected production incoming uses satisfy the narrower
invariant that every live row stays at level 1, so their extrusion calls change
no row levels. Neither observation proves source permission law (L): the code
facts do not define the source admissibility predicate, represent existential
request permission, or validate every derived comparison against the selected
source guard.

The result reduces the stale-level objection to an entry-state or omitted-owner
objection. It does not close the source bridge or certify this note independently.

## Baseline, authority and dependencies

The primary supplied the baseline above. No Git command was used to verify the
commit, branch or tracked-file equality. Frozen SHA-256 hashes below identify
the exact live files read; the primary must compare them with its pinned input
snapshot before integration.

Rules read in full: `rules/research-lab.md`, `rules/design-authority.md`, and
`rules/git-concurrency.md`. Relevant routing context was read from
`tasks/research-lab.md`, `tasks/current.md:479` vicinity and design-index
locators. These coordination records are not theorem premises.

Exact governing sections:

- Contextual valuation note: P1–P4, “Exact transition correspondence and
  preservation”, “Compose the actual incoming route without changing the
  caller”, and “Extrusion, source permissions and diagnostic ownership remain
  explicit”, including (L).
- Production reduction: “Exact named scheme and incoming-use reduction”,
  “Symbolic effect elimination and finite structural lemma”, and its explicit
  source/denotation boundary.
- Redesign charter §§1–4 and §§22–23: F5 is comparison material; every derived
  existential comparison re-enters the source level guard; levels belong to
  variables rather than constructor heads. These selected directions are
  retained, not redefined.
- F5 comparison foundation §§9, 22, 23 and 32: incoming substitution/restoration,
  live task algebra, allocation levels and the named recursive scheme, and
  opaque closed observations. These identify legacy production owners rather
  than select successor source meaning.
- Concrete compatibility boundary §§1 and 3: one endpoint-directed inequality;
  arbitrary concrete successes do not compose into a structural preorder.

The candidate regular-tree carrier, one value shared by both row polarities,
complete Function variance and the same-assignment extensional result remain
the contextual note's conditional premises. This lane neither proves nor
changes them. No question-board bundle or unfinished worker artifact was used.

## Claim classes and exact premises

**Static characterization:** the production owner locations below have the
stated allocation, aging, insertion and replay order. This is a source read,
not an executed test, acceptance observation or source-semantics oracle.

**Conditional invariant derivation:** start with empty live inventories, or an
entry state already satisfying invariant I below. Permit only valid,
well-polarized, finite acyclic pure constructor syntax, live row identities,
empty-row allocation, `constrain_live` and its inspected value/extrusion owners.
Constructor identity and fields are immutable. Installed row cycles are allowed.
Observe only successfully completed operations; no failed/interleaved extrusion,
external inventory injection, row retargeting or partial observation is included.
Arbitrary allocation levels are allowed for this derivation. It proves a property
of syntactic stored-row dependencies, not of the rigid names inside a semantic
valuation.

**Narrow production characterization:** for an ordinary collected batch through
its inspected non-test allocation/aging owners, all row levels remain 1. This
uses the actual collector's `use_level: 1`; it is not a claim about future nested
source bodies, test-created recipes or a successor algorithm.

**Conditional permission consequence only:** if admissibility depends solely
on a fixed source environment, the same row identities/assigned values and
unchanged level/permission coordinates, and those are in fact its complete
inputs, equality of those coordinates implies equal admissibility. The missing
source interpretation and comparison-guard premises cannot be supplied by this
identity argument.

## Installed-inventory invariant I

For a stored non-variable pure payload t, let `vars(t)` be the live value-row
ordinals occurring syntactically in its finite Function fields. This does not
expand a row's installed bounds. Pure effect leaves have no live row ordinals.

At a successful operation boundary require:

```text
I.1  For every exact lower or upper payload t stored on v,
     and each w in vars(t): level(w) <= level(v).

I.2  For every stored direct edge v -> w: level(v) = level(w).
     Both adjacency copies represent that same edge.
```

Consequently every row reachable from v by following exact-payload occurrences
or either direct adjacency direction has level at most `level(v)`. This is
ordinary finite path induction: I.1 never increases levels, I.2 preserves them.
It does not require row-bound acyclicity and does not interpret an inequality.

### Why guarded extrusion preserves I

Consider a completed `extrude(t,k)` from an I state. A reached row with level
at most k may be skipped: every installed descendant already has level at most
that row's level, hence at most k by path induction. A row with level greater
than k is set to k and then all exact lowers, exact uppers and both adjacency
lists are pushed. Constructor endpoints push their fields. Every descendant
that still exceeds k is therefore eventually lowered; the generation mark only
skips work already processed under this same fixed k.

On completion, every syntactic row occurrence in t and every row reachable
through its installed inventory has level at most k. For I.1, if an owner was
lowered, its payload descendants were reached or safely skipped and are now at
most k. If only a dependency was lowered, its inequality against an unchanged
owner becomes weaker. For I.2, lowering either endpoint visits its direct
neighbor; their previously equal levels are both lowered to k. Unvisited
relations retain their old levels. Thus I holds again.

The invariant can temporarily fail after setting an owner's level and before
processing its pending children. The proof is expressly at completion. Stack
reservation failure or journal failure before completion is excluded; rollback
and discard correctness are separate obligations.

### Why the mutation owners establish I

- Startup and `fresh_value_at_level` allocate empty rows
  (`yu-solver/src/lib.rs:9487`, `:9522`, `:9550`). Allocation establishes I for
  the new row and changes no existing relation.
- For a non-variable/row pair or its dual, `constrain_live` performs payload
  extrusion at the receiving row's level before memo admission and before
  `apply_value_task` stores the exact payload (`:11126`–`:11160`,
  `:12155`/`:12223` vicinity). The completed extrusion makes every syntactic
  dependency at most that receiving level; subsequent storage establishes I.1.
  The receiving level itself cannot decrease below the fixed extrusion target.
- For a row/row pair, `apply_value_task` computes the endpoints' minimum level,
  extrudes both endpoints to that fixed minimum, then installs both adjacency
  copies (`:12077`–`:12121`). Both endpoint levels equal that minimum on
  completion, establishing I.2. Existing payload and adjacency relations retain
  I by the extrusion argument.
- Bound replay queues fresh comparisons through `constrain_live`; those
  comparisons use these same owners. Function decomposition stores no inventory
  relation itself; its children re-enter the same dispatch. Duplicate memo hits,
  extrema terminals and incompatible-head terminals make no level/inventory
  mutation. No additional insertion owner was found before the test module.

This is an induction over completed owner operations. Cyclic exact lowers such
as the recursive scheme's own lower are covered. It is not an argument that all
arbitrary inventories allowed by the extensional note's P2 satisfy I; P2
explicitly permits arbitrary levels and does not require owner reachability.

A falsifier for I must therefore expose an omitted production mutation owner,
mutable constructor fields, a reachable non-I entry state, or an unsuccessful
operation later treated as committed. Merely adding a larger cyclic inventory
without its creation trace does not discriminate this claim.

## Exact incoming trace and the stronger collected-state restriction

The relevant production owners fix all collected component and parameter rows
at level 1 (`:9471`–`:9530`). Collection freezes every `DefinitionUse.use_level`
as 1 (`:1107`–`:1133`). The only non-test `fresh_value_at_level` call sites
found are the Q/R allocations in `instantiate_and_route_closed_inner`
(`:14536`, `:14564`), both using that frozen use level. `child_level` at :9614
has no non-test call site. Normal extrusion only lowers levels to a receiving
row level or the minimum of two row levels; it creates no smaller independent
level. Thus induction gives level 1 for every value and effect row throughout
these collected production sessions. Rollback restores previous levels; it
supplies no different successful initial level.

For either member of `my f x = g; my g y = f`, the supplied exact scheme is
`Q=[]`, one R binder, predicate and lower
`L=P0(Top-,P0(Top-,rho+))`, upper Top. The smallest incoming owner suffix is:

| Step | Created/stored/replayed relation | Levels |
|---|---|---|
| 0 | Already allocated occurrence row cu and its complete caller inventory | cu=1; all existing rows=1 |
| 1 | Allocate one empty fresh rho for R at `use_level` | rho=1 |
| 2 | Restore `L <: rho`; extrude L at level(rho), encounter rho and safely skip; store L as rho's exact lower | unchanged |
| 3 | Restore `rho <: Top`; Top terminal stores no exact upper | unchanged |
| 4 | Route `L <: cu`; extrude L at level(cu), encounter rho and safely skip; store L as cu's exact lower | unchanged |
| 5 | Replay against cu's exact uppers/direct upper rows; all resulting row insertions and Function subpairs use the same owners | unchanged at every completed step |

No direct `rho -> cu` edge is invented. For an existing upper
`cu <: N0(A0+,N0(A1+,v-))`, replay decomposes the two Functions, emits the
true pure effect pairs and argument-to-Top pairs, then submits `rho <: v`.
The direct-row owner ages both to min(1,1), which skips both, then installs
`rho -> v`; both remain 1. Other existing upper payloads or direct neighbors
can generate further replay, but never a target level outside the invariant.
The cycle through rho's lower is a stored row cycle, not cyclic constructor
syntax. No allocation or edge in this suffix reaches a younger descendant.

This is a symbolic owner suffix under the audited exact-scheme premise, not a
new executed source fixture with an external use. The source fixture in the
production reduction establishes the member scheme separately. Even with
arbitrary-level allocation permitted in the broader owner derivation, I
excludes a younger installed descendant behind an older skipped row.

## Source permissions: the precise remaining blocker

The open law is still the contextual note's

```text
R_initial(sigma) /\ F2(d)<=d /\ d<=Top /\ F2(d)<=sigma(cu)
  => [A_alloc(sigma,d) iff A_final(sigma,d)].                 (L)
```

I establishes only syntactic level closure. A semantic assignment d may contain
rigid names not represented as syntactic live row ordinals in a payload.
Consequently I supplies no theorem that a level-lowered row retains all allowed
source assignments. The all-level-1 restriction avoids actual level changes for
this collected route, but does not establish that these legacy levels realize
selected source scopes or that A's only changing input would be a level.

In particular, `LiveVariableMetadata` at :749 distinguishes `Collected`/`Fresh`
and a `non_generic` flag; it provides no source request-existential/rigid
permission interpretation. The inspected `constrain_live` dispatch has terminal
and ordinary structural/row branches rather than a source judgment for the
charter §22 guard. Extensional truth of a replay task does not establish its
source permission, even if no stored level changes. Code coverage of these
owners therefore cannot replace the selected requirement that every derived
existential comparison re-enters that guard.

No affected source permission is exhibited, because no admissibility-falsifying
source assignment/guard trace has been established. Reporting a source
counterexample from absent legacy permission machinery would silently assume
that this comparison compiler implements the successor contract. Conversely,
reporting (L) as proved from unchanged legacy levels would silently assume its
missing source interpretation. Both implications remain unverified.

Recommended next action: supply a source-derived definition of A and its mapping
to the exact admitted occurrence-row class, including the guard on replayed
comparisons. Use the all-level-1 production characterization to decide whether
a bounded no-level-change (L) lemma applies; use I only to discharge the guarded
traversal's installed-row closure premise when future heterogeneous levels are
actually in scope.

## Independence, coverage and resource accounting

There is no executable reference, checker or source oracle in this lane. The
owner-order audit uses production code independently of a toy transition model;
the invariant shares those inspected transition rules and immutable-term
premises. It proves their consequences, not their selected source denotation.
The regular-tree valuation theorem is a dependency, not an oracle used to
certify source permissions.

Coverage is symbolic induction for all finite successful pure owner traces
under the stated premises, plus the exact one-R incoming suffix. No bounded
enumeration, seed/range, mutation execution, test, build, benchmark or parser
probe was run. The inspected level/inventory-write and allocation call-site
searches span `yu-solver/src/lib.rs`; this is not an exhaustive repository-wide
mutation or unsafe-code audit. Omitted cases include injected test inventories,
future nested levels, request existential representation, effectful payloads,
concrete adaptation/Records, mutable external term owners, failures,
interleaving, source realization, diagnostic completeness, acceptance,
principality and publication.

Commands used: `cat`, bounded `sed` and `rg` reads, `sha256sum`, and a final
leased-note/dependency integrity read. Some initial combined captures were
truncated; the owner branches and governing sections used above were reread
narrowly. One mistaken guessed compatibility filename did not exist; the exact
2026-10-03 locator was then read. No Git/index/ref command, child delegation,
compiler edit or executable probe was performed.

Budget consumption: one lightweight shell process at a time; zero builds/tests,
zero search shards and one note output. Individual read/hash processes reported
subsecond wall time. Total agent wall time, peak CPU and peak RSS were not
measured; no numeric resource-use claim is made. No explicit numeric wall-time
or memory cap was supplied in the assignment. Writes stop at this frozen note.

## Frozen dependency hashes

```text
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
f7351170386a2b832ccd5bfccec32ad46fab3c7ab6bf42b9387ea39f1ecae53b  notes/progress/2026-10-06-live-row-contextual-valuation-attempt.md
f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779  notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  notes/design/2026-10-03-concrete-compatibility-boundary.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
```

## Commit packet

- Exact leased changed path:
  `notes/progress/2026-10-06-rec-name-return-level-permission-reachability-falsification.md`.
- Baseline SHA: `62560fbbc2d69971a80afec95fd34858c763024b`, supplied by primary;
  baseline-object/file equality remains primary-owned.
- Changed dependency hashes: none observed between initial and freeze checks;
  exact hashes above. No dependency was written by this lane.
- Claim/review status: frozen, independently reviewed research-only owner
  characterization and conditional invariant derivation; no source permission
  theorem, gate completion or implementation authority. The review covered
  both level-permission notes and cited owner paths, not source-denotation or
  failure/rollback proofs.
- Checks already run: narrow owner/call-site reads; dependency SHA-256 equality;
  leased-note text integrity. No tests, builds or Git checks.
- Proposed one-line checkpoint message:
  `research: characterize recursive incoming level reachability`.
- Shared-record deltas intentionally left for the primary/curator: record the
  installed-payload/direct-adjacency level invariant and the collected
  all-level-1 restriction; retain (L), source realization and target selection
  as open. No shared task/index/theory/question files were changed.
