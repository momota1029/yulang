# Cycle 241: independent design review of stable-name rebase

## Scope and decision status

Read-only review of I-47 at integration `1c675172`, including I-45/I-46.
The refuted 239 and 240 targets stay stopped. No successor implementation or
new Lean declaration is supplied by this note. This is a review of option (a),
not a selection made independently of the comparison requested by I-47.

**Conclusion:** stable names are promising for stopping name growth, but
allocation ownership is not semantic privacy in the current journal. Replacing
only the current ordinary merge atoms is insufficient. A conservative design
needs an explicit scoped definition store and a projection/transport invariant
covering historical plans, observations, child inputs, outputs and aliases.
Finite identifiers alone are not a termination argument.

## What the existing code actually records

* `VersionedAllocation231.Fresh` permits a collision when its key is already in
  `allocated`. It does not state absence from semantic support, exclusive use by
  one plan, or absence from another plan's right-hand sides.
* `VersionedInstallation231.atoms` combines cross-compatibility, aggregate
  equations and report self-checks. Only the aggregate equation chunk is a
  candidate definition store. Cross and self-check constraints must not be
  erased wholesale: they can constrain original sources directly.
* `VersionedInstall232.installCore` appends raw sites, centered sites, children
  and packets, and installs the replay context. `install` also appends the full
  plan and effect to the journal. `VersionedJournal232.Models` requires **every**
  historical plan's full `Holds`, as well as historical/current effect semantics.
  Thus deleting an atom from current ordinary does not remove its old plan's
  merge equation, or its occurrence inside captured historical contexts.
* `VersionedPlans231.Inputs` includes merge equations, capture-to-actual fits,
  head sharing, child-site semantics, child schemas and nonactual emitted
  equations. `Outputs` includes the complete generated output schema. A rebase
  must not restore the old defect of dropping part of this total contract.
* `VersionedFrame231` keeps actual centers and output/child allocation distinct
  from purpose-0/1 aggregates. This separation is valuable and should remain.
  It does not make aggregate values unobservable: lower/upper materialization
  and emitted child bounds read those values.
* `VersionedJournalFrame236.sources` explicitly includes full historical packet
  support and both recorded/current class supports. Its assignment-patching
  theorem requires semantic support disjointness, not an allocated-key test.
  `SelectiveEquationRealization236` similarly preserves a protected pool and
  requires every reused target already to satisfy its equation. It cannot be
  cited as permission to overwrite an escaped target.

## Escape already witnessed by the actual 240 trace

`LooseLoopRefresh240` exposes the first aggregate lower as base source slot 5.
`LooseLoopRetarget240` then moves the root's lower endpoints from source 2 to
that aggregate while preserving upper source 4. This is an actual new-boundary
source path, not a hypothetical malformed state. Consequently the original
source, the *current* base source map, and private allocator names are different
notions. Being outside the original five sources is not sufficient privacy.

With a stable lower name L, a later rebase can have a right-hand side containing
L itself: the repeated capture lower becomes union(L,L). Its defining equation
is then semantically just L=L. The old relation L=x cannot safely be discarded
on the basis of fresh naming alone. In the particular 240 model other facts may
still force both to Foo(Int); that does not prove a general dependency theorem.
The source of this hazard is visible without inventing a language-level failure.

## Small algebraic tests for naive formulations

These are mathematical tests of proposed invariants, not newly verified Lean
regressions and not a refutation of every possible rebase architecture.

1. **Pointwise full-model preservation already fails for an isolated definition.**
   Old store L=x and new store L=y have the same existential projection onto
   x,y when L is otherwise unused. But choose unequal values for x,y and set
   L=y: this is a model of the new store, not the old store. Thus the existing
   same-assignment `Models after m -> Models before m` theorem cannot be justified
   merely by saying L is private. Projection or a model-transport map is needed.
2. **An escaped name can constrain public values.** Old store L=x plus retained
   external constraint L<=z projects to x<=z. Replacing the definition by L=y
   projects to y<=z instead. With x=Int, y=Top, z=Int, one direction is lost;
   with x=Top, y=Int, z=Int, the other direction is lost. A namespace owner alone
   cannot justify either refinement direction.
3. **Self-reference loses a definition.** Replacing L=x by L=union(L,L) makes
   the defining equation tautological. Retained L<=z then need not imply x<=z.
   To rule this out, normalize dependencies to a protected external support or
   prove a well-founded definition graph. A syntactic one-owner label does not
   rule out the self-reference exhibited by retargeting.

## Exact theorem obligations for a viable option (a)

Let O be an explicitly defined protected observation support: original source
identities, actual centers, public outputs, and any endpoint whose value has
escaped to retained obligations. Let D be a scoped aggregate definition store.
A proposed rebase transaction replaces one owner's slice and atomically
reconstructs every dependent consumer.

1. **Definition elimination / projection.** For every source assignment s,
   prove `ProjectedModels(state,s) iff exists m, Agree O m s and FullModels(state,m)`.
   The underlying elimination theorem must prove simultaneous extension for all
   owned definitions, with coherence and an acyclic dependency order or an
   explicitly justified solution of cycles. It must preserve rows and actual
   centers, not just the types at two fresh names.
2. **Transaction frame / no lost obligations.** After rebasing, every retained
   constraint outside the replaced definition slice is preserved under a
   model-transport map fixing O. Consumers mentioning the slice must either be
   reconstructed with a proved transport theorem or included in the owned
   transaction closure. This includes current raw observations, historical
   packet contexts, `Inputs`, `Outputs`, class effects, child sites, aliases,
   trusted facts and their readback certificates. Merely replacing the newest
   plan does not update all older snapshots.
3. **Observable refinement and evidence transport.** Prove projected models
   after are included in projected models before for a real update, and iff
   for representation-only rebase. Also transport the dictionary/diagnostic
   observations and protected output equalities. This is not automatically the
   old full-assignment model-back statement; a new boundary must state exactly
   which representation of Model makes the original language observation
   contract unchanged.

An alternative is much stricter exclusive ownership: no target appears in any
retained consumer outside its own slice, and all RHS supports avoid the slice.
Then existing finite equation extension tools nearly provide the elementary
projection result. That invariant is false for the current refresh/child
pipeline, so adopting it requires a representation redesign, not a new proof
about unchanged states.

## Termination skeleton, and the remaining gap

Stable per-invocation/per-declaration keys bound the number of aggregate IDs
only after the invocation bound is proved. The earlier finite invocation/center
results may help, but their ground-model and child readback hypotheses must be
preserved by the projected semantics.

For full Acc, exhibit a finite set F of observable obligations, show every
nontrivial transition permanently adds a member of F, and prove rebases preserve
all previous members. Equivalently provide a finite-height information order
and a strict increase for each enabled semantic update, with representation-only
transactions excluded from the progress relation or handled by a separate
well-founded administrative normalization. Existing 236 administrative Acc can
be reused only through its actual preserved-fact hypotheses.

Finite names, finite equations at each instant, or even a finite state space do
not exclude cycling: a rebase can alternate L=x and L=y. Monotonicity of model
sets alone also needs a finite-height argument; an infinite semantic lattice
can have an infinite descending chain. The RHS syntax/observation support must
have a genuine bound derived from source mass or another proved finite basis.
No such general bound is established by this review.

## Regression obligations

* 199: retained semantic/class conflicts must survive projected rebasing; no
  erasure of a prior public contradiction when its private proof is replaced.
* 202/204: default and explicit-output total packet semantics remain complete;
  changing aggregate ownership cannot drop output equations or evidence.
* 206: preserve its existing intended pending/obstruction behavior and full
  model witnesses; private cleanup must not manufacture a dictionary.
* 218: preserve actual shared-head consistency and distinct source obligations.
  The latest root selected-with-pending-child result must not be silently turned
  into a completed dictionary; old conflicting child rejection must survive.
* 230: primary rebase stress test. New observation-dependent definitions must
  replace their owned old interpretation without reviving the old stale-merge
  inconsistency, while source demand, outputs and legitimate refinements stay.
* 239/240: stable names plausibly remove the demonstrated endless fresh-name
  progress, but the new literal self-dependency above must be handled. Blocking
  the old exact sequence is not a general Acc theorem.

These are acceptance obligations, not proved new regression outcomes. Existing
frozen regressions remain untouched. I-45 can provisionally remain as an
independent literal-point rule; it neither supplies ownership nor solves the
rebase termination measure. Removing it would need an explicit comparison of
observation transport and intended refinements.

## Recommendation to the parent comparison

Do not select the minimal 'replace current merge atoms' design. If (a) is chosen,
choose an explicitly scoped, dependency-aware definition-store design with
observable projection and a finite-progress theorem as its first proof targets.
It is more concrete than a semantic quotient over all carrier values, but not
cheap. If neither the projection invariant nor a finite observation basis can
be specified without changing accepted programs, stop and ask the supervisor;
do not call finite private IDs a termination proof.
