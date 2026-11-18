# I52 rebase successor Step — partial implementation plan

Latest integration a44b8b310, read14:55 UTC. Stop adding old-family finite Views.
This design supersedes the earlier research priority, not its verified results.

Finite representation: fixed finite candidate fact universe, in canonical order.
Facts identify an owner's lower basis atom, upper basis atom, fixed binder fact,
or installed flag. Store a canonical sublist of facts not yet present; derive
normal-form atom lists by selecting present facts from the fixed universe.
Owner slots are fixed by the layout. No historical definitions or fresh private
slots are appended. Writing an owner updates its selected atom sets in place.

Partial executable step: an observation/compiler function returns a finite list
of proposals, each a finite list of facts. A proposal removes those facts from
remaining. A Step requires this removal to change remaining, so an unchanged
observation has no transition. The generic observer is an EXPLICIT parameter:
no all-source observer/compiler or its semantic correctness is claimed.

Measure: remaining.length strictly decreases. Prove structural Acc for every
observer, but distinguish it from Acc of a language-faithful complete kernel.
The latter needs the missing observation/installation correspondence.

Concrete I45 regression: one owner, fixed initial basis, fixed binder equations,
one proposal corresponding to the canonically transported terminal packet.
Commit once; all later identical proposals are no-ops. Relate the two reachable
states' public model projections to the old initial/positive family using the
already-proved uniform reconstruction. This supplies a genuine partial Step
with a concrete stopping regression, not a relabeling of the nonterminating
old Step. 239's complete observation bridge and general source completeness
remain open unless proved explicitly.

Representation choice: canonical remaining-fact sublists avoid function
extensionality in executable change detection. An owner-indexed bit vector is
an equivalent future alternative; no language semantics is selected here.

## Verified partial successor, 15:03 UTC
Three modules now define the real finite-state write relation and prove `Acc`
for every supplied observer by strict remaining-list length. The concrete I45
terminal observer has one eligible fixed proposal. It installs once, reaches
five fixed facts, cannot take a second step, and every positive old completed
stage projects to that terminal state. A separate theorem proves sound and
complete public-model correspondence for each completed I45 stage, preserving
all initial components 0..4 and all rows, allowing the private binder to change.

This is a partial successor, NOT a faithful general source kernel yet. The
observer is an explicit fixture table, not a proven compiler from general
inspection. Models formally assigns its else predicate to every noninitial subset; only
the two reachable fixture states have a proved correspondence, and arbitrary
intermediate subsets have no claimed language interpretation.
No simulation of all old administrative microsteps, complete constructor or
presence handling, 239 concrete correspondence, general source fixed basis,
or general semantics-preserving termination theorem is established. The proved
Acc applies to this newly defined gated relation only, not the old Step.

## Numeric and duplicate-install regression
`GeneralRebaseBudget258.Runs` counts actual new Step edges. The run length plus
remaining facts is at most the initial remaining count. Starting from initial,
there are at most basis.length steps; in the I45 fixture at most one. Rewriting
the same proposal is idempotent and `tryWrite` then returns `none`. These are
properties of the defined new relation, not an assertion that every source
observation is represented, nor a bound on old microsteps or running time.
