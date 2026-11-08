# B4: outer interval resolver

Status: Draft implementation contract, 2026-11-08. This is a top-down,
conditional outer layer, not B4 E1. Authority: `spec/06-roles.md` 6.2–6.5,
`spec/04-types.md` 4.3, the owner decisions recorded in the recovery handoff,
and the interval rules in the two Yulang2 reference notes. No new language
decision is made here.

## Data and the remaining boundary

A request contains a demand `(role, arguments)`, the current ordinary
type/row constraint graph, graph/slot identities and levels, and an origin.
Every argument has two endpoints `(lower, upper)`; there is no stored centre.
The caller fixes one finite list of visible impl declarations for the whole
resolution. Each declaration has an identity `k`, its role and head templates,
all its ordered where templates, and its associated equations in the same
annotation-variable scope. The root caller's visibility does not change for
children. A child request includes the propagated constraint state, not just
a type substituted into a head.

The outer module abstracts this state as `Request` and its immutable visible
environment as the closure of a `Protocol`. This abstraction is deliberate:
the repository does not yet construct the above state from source. The
executable `frontier : Request -> Frontier Request` must return one of
`pending`, `rejected`, `ambiguous`, or `selected k children`. The independent
`Local : Request -> Frontier Request -> Prop` below specifies that boundary.
`FrontierExact` is an **explicit, undischarged bridge hypothesis**, not a field
whose truth is assumed silently. So is accessibility of generated where
requests. Supplying a table of expected answers does not discharge either
bridge for Yulang input.

## Independent judgments (no reference to the resolver)

At a fixed snapshot, `Local q f` means:

* pending: the lower head needed for the demand or a required decomposition
  is unresolved; a concrete upper alone cannot start resolution;
* rejected: the reached root is an anonymous regular type; or an otherwise
  surviving visible head must inspect such a constructor (K2); or ordinary
  propagation eliminates all candidates;
* ambiguous: no K2 rejection, no unresolved inspection, and at least two
  visible declaration identities survive propagation;
* selected `k children`: no K2 rejection, no unresolved inspection, exactly
  declaration `k` survives, its associated equations have been propagated,
  and `children` is the complete ordered list generated from its where list.

The independent outer `Classify q result` has rules for the three terminal
local judgments. For a selected local judgment it requires independent
`Classify` derivations for **every** child, in order. If all children return
finite dictionaries `ds`, the result is `selected (node k ds)`. A pending,
ambiguous or rejected child prevents a completed dictionary. `All₂` records
the ordered child derivations and `Combine` their outcome without calling
the resolver. `Frontier.selected` remains distinct from dictionary completion.

The implementation returns a *frontier tree* containing the local decision
at every visited demand. The public `classification` projects it into these
four outcomes, using a finite dictionary only when all children succeed.
For multiple child failures the tree retains all outcomes; the projection
uses rejection, ambiguity, then pending priority. This order is only a
summary of already failed obligations, not candidate filtering, diagnostic
selection, or a reason to omit a child. It is a generic protocol policy,
not a priority rule derived from the specification. The K2 priority rule in
the specification concerns candidates of a single demand. Alignment of the
projection with a source-level outcome judgment is still required.

## Executable entry and exactness

`resolve protocol request accessibility` inspects exactly one frontier.
Terminal frontiers return immediately. A selected frontier recursively maps
the same entry over **all** its children and constructs a finite tree tagged
with the actual declaration identity. The recursion is on `Acc` for the
independent child relation

```
Child Local c p := exists k cs, Local p (selected k cs) and c in cs.
```

This is proof-directed well-founded recursion, not a fuel limit, role rank,
caller-chosen depth, or a coinductive dictionary. Accessibility is not yet
derived from declaration checking. There is no general source resolver
claim until that derivation and `FrontierExact` are proved.

The implemented recursion is over **fixed** child frontiers. A child returns
a tree, not an updated ordinary graph. Therefore this implementation does
not yet thread a child's associated/ordinary constraints into its siblings
or recollect its parent after those constraints change a snapshot. A source
resolver must add that lifecycle or prove a shared, saturated snapshot
adequate before applying this outer theorem. This is an additional explicit
source bridge, not something guaranteed by the arbitrary `Request` type.

Exactness, with all quantifiers:

```
for every Request : Type u,
every protocol (frontier, Local),
every exact : forall q f, frontier q = f iff Local q f,
every q : Request,
every accessible : Acc (Child Local) q,
and every result : Result,
  classification (resolve protocol exact q accessible) = result
    iff Classify Local q result.
```

The tree theorem states the analogous iff against the independent `Resolves`
judgment, before projecting failures. Thus exactness is independent of the
executable recursion and also checks the selected keys and the full ordered
child tree. The hypotheses are intentionally visible in theorem names and
types; this is not the unconditional E1 statement for B4.

## Interval propagation, K2, and all where children

The missing frontier bridge must be proved from **generated constraints**,
never `exists assignment, head[assignment] ~ goal`. Captures retain endpoint
pairs. Repeated captures of a name coalesce their lower endpoints by join
and upper endpoints by meet. For every pair of occurrences A,B, propagation
includes `A.lower <: A.upper`, `B.lower <: B.upper`,
`A.lower <: B.upper`, and `B.lower <: A.upper`. The original ordinary atoms
are retained and each candidate is tried in its own state. Applicability
comes from this propagation, not from searching point assignments. Statements
about solver models quantify assignments to the generated constraints only.

Same-head interval endpoints lift that constructor and pair its argument
endpoints recursively; different heads remain an interval. Once within an
invariant argument, used covariant and contravariant children are also
intervals. This nests without a depth bound. Unknown structure and record
tail subtraction are deferred; unsupported syntax is not language pending.

K2 is checked after ordinary incompatibility has eliminated an unrelated
candidate, and before counting surviving heads. An anonymous regular *root*
rejects before resolution, even for a variable head. A non-variable head
that must inspect a regular descendant rejects the entire demand before
ambiguity. Plain variables and all names in a merged-variable payload
capture the whole payload without inspection. Named recursive types match
their nominal identity; the body is never opened. Graph changes require
revalidation of these observations.

For a selected declaration, construct one binding per head name by merging
**all** its captures. Substitute that pair into every occurrence in **every**
where template and associated equation, preserving sharing, order, kinds,
levels and caller visibility. Missing names are an admission failure, never
a default binding. Propagate ordinary equations, then construct all child
requests. A completed dictionary contains the actual selected identity and
one completed finite dictionary per original where clause. A child's failure
does not cause backtracking to another parent impl.

## Identified reuse and exact outstanding bridges

The outer recursion itself uses only Lean. The following existing results
are candidates for discharging the source bridge; they have **not** been
connected to this entry by the present implementation.

* `CommonRoleIntervalGeneration.generate_exact`: all self/cross ordinary
  atoms exactly express coalesced interval consistency.
* `CommonRoleRepeatedCaptureChecks.merged_eval`, `merged_valid_iff`, and
  `generate_exact`: merged endpoints and repeated-name constraints.
* `CommonRoleCandidateConstraints.generate_exact`, `solve_all_instances_exact`,
  `generated_prepare_all_instances_exact`: actual ordinary family solving.
  These do not establish applicability or graph/slot provenance.
* `CommonRoleGraphBisimulation.regular_at_exact`,
  `CommonRoleGraphInspection.inspect_all_cycle_sound`, `shared_opaque`,
  `snapshot_unknown_exact`: regularity and opaque-capture observations.
* `CommonRoleDeferredBounds.lowerHeads_exact` and the origin-preserving
  graph snapshots: actual lower-bound provenance, not candidate selection.
* `CommonRoleCanonicalRows` / `CommonRoleStableRecordResidual`: canonical
  concrete record subtraction; unknown tails still require scheduling.
* `CommonRoleStablePaterson.check_sound` /
  `CommonRoleIntervalPaterson.every_where_decreases`: finite Form arithmetic,
  not yet the richer graph/merged-interval descent.

Required bridges for unconditional B4 E1:

1. `source_frontier_exact`: construct source graph/slots, perform complete
   head/goal interval propagation (including root constraints and K2 priority),
   substitute merged bindings into the entire actual where/associated list,
   and prove the resulting `frontier` equivalent to the above `Local` rules.
2. `checked_interval_children_accessible`: for every declaration-checked
   registry and source request, prove `Acc (Child Local)` from stable Paterson
   checking and K2 on the richer interval carrier. No assumed role rank.
3. Source adequacy for `Local` and the qualified output family, including
   updates/recollection, associated equations, generalization and levels.
   In particular prove `where_state_recollection`: all children share the
   actual ordinary graph, updates caused by one are propagated to siblings
   and parents, and fixed-frontier evaluation is used only when that snapshot
   is stable. Otherwise replace the independent child map by a state-threading
   driver and prove its transition relation exact.

X6 and X8–X12 become PROVED only after their *actual inputs* instantiate the
frontier and accessibility bridges through this entry. Tests with supplied
frontiers test the outer protocol and must not change those conformance
statuses. The task's hard prohibition on editing existing Lean files also
keeps `SpecExamples.lean` unchanged until a permitted additive replacement
has genuine conformance theorems.
