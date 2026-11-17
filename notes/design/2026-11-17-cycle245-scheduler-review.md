# Cycle 245: actual table scheduling and the missing simulation

This is a read-only design review of Scheduler242, SchedulerOrder242,
Progress241, Machine241, OwnerTable244, and UsedSupport245. Examples below are
constructor-level calculations, not newly checked Lean declarations. No solver
termination or EvidenceNode result is claimed.

## 1. Active checks are not an inductive scheduling invariant

Use three distinct owners with singleton type-definition blocks:

- A: target 2, RHS `var 4`.
- B: target 3, RHS `var 2`.
- C: target 4, RHS `var 3`.

Every block is External and Coherent, and owner targets are pairwise disjoint.
Every ordered pair of distinct blocks passes `activeCheck`. For example, A
into B replaces its sole typed read 2 by RHS 4, which avoids B's target 3;
A into C does not select an A lookup. The other four cases rotate this same
argument. Thus even checking all currently possible owner pairs does not
exclude a three-owner dependency cycle.

Rebase A with the fresh block `[2 -> bottom]`. This fresh block is External,
Coherent and uses precisely A's former target. All checks required for this
particular step pass. Actual OwnerTable244.rebase produces:

- A': `2 -> bottom`.
- B': `3 -> var 4`.
- C': `4 -> var 3`.

All resulting blocks remain External, Coherent and target-disjoint. But
`activeCheck B' C' = false`: C' reads type variable 3, whose selected B' RHS
is variable 4, exactly C's target. The symmetric check C' into B' also fails.
The first rebase collapsed a three-cycle into a two-cycle. Consequently neither
old all-pairs active checks nor fresh External/Coherent/TargetsWithin imply
all-pairs active checks after rebase. This is not the old check's unused-RHS
false positive. The selected RHS would really introduce self-dependency.

This is an algebraic counterexample to those interface hypotheses, not a claim
that this state is reachable from actual language operations. A producer might
exclude it through a proved source-dependency invariant. That invariant is
precisely missing, and cannot be silently assumed from finite identities.

There is also a mixed-coordinate two-owner example:

- A: `2 -> bottom`.
- B: `3 -> arrow bottom (row.var 2) bottom row.empty`.
- Fresh A: `2 -> var 3`.

Initially both active checks pass: B has no typed read of 2 and A has no typed
reads. B is unchanged by rebase A, since the substitution preserves rows.
Fresh A is External. The next B-into-A check fails: A reads type 3, whose B RHS
contains row source 2, A's own target. A type-only dependency graph would miss
this case. A graph used to imply current External must account for row sources
inside inserted RHSs, or deliberately refine the External invariant and prove
that separate refinement soundly.

## 2. Why the existing scheduler theorem does not instantiate directly

Machine241.service only replaces the selected block and drains its dirty bit.
Its `service_other` and `public_unchanged` are literal equalities. Scheduler242
uses `service_other` to keep every previously clean owner's block equal to
`compile facts owner`. Its learning step leaves the table unchanged.

Actual OwnerTable244.rebase substitutes into every base atom and every other
owner's RHS, then installs the fresh selected block. Thus its base and other
blocks need not be literally unchanged. A model readback relation, even the
new one-way Models result, is not a proof of those syntactic equalities.

SchedulerOrder242.tables_unique furthermore requires a fixed deterministic
`compile` of the fact set and exact clean-block equality. Its fact uniqueness
uses monotone discovery on a fixed finite domain. It does not establish that
actual source discovery has such a domain or is a function of facts alone.

## 3. Minimal interface for actual finite termination

For termination alone, avoid unnecessarily simulating the syntactic table.
Project an enriched actual state into the finite Progress241 work state:

1. Fix finite fact and owner indices for the entire run; identify actual owners
   with those indices. Give an actual-state projection `work` and a reachable
   invariant. Owner identity stability must be proved, not counted afresh.
2. Prove invariant preservation for every actual transition.
3. For every actual transition, prove either:
   - facts are retained and at least one previously false finite fact becomes
     true; arbitrary dirty changes are then paid for by that strict progress;
   - facts are unchanged and the dirty count strictly decreases. To reuse the
     existing Progress241.Step constructor directly, show exactly one pending
     owner is drained and all other dirty bits remain unchanged.
4. Account for every actual transition, including refresh, revisiting changed
   consumers, no-op service, blocked-check recovery, cache/inspection work and
   any representation normalization. A step that leaves the projection fixed
   cannot be erased without an independently well-founded local measure.

The resulting rank is
`absent facts * (ownerCount + 1) + dirtyCount`.
The maximal rank from an arbitrary work state is
`factCount * (ownerCount + 1) + ownerCount`.
Strict rank descent would bound the number of actual counted transitions by
that number. This is a conditional design calculation, not a proved bound on
actual runs. A stuttering simulation with only non-increase does not suffice.

This Progress-only interface allows actual syntax to change extensively. It
still requires the difficult claim that changed clean consumers do not need
unpaid work. Marking all such consumers dirty without adding a genuinely new
finite fact can increase this rank. Repeated history/version stamps cannot be
used as fresh facts while retaining a fixed finite fact domain.

## 4. Additional interface for meaningful completion and order independence

A rank proof alone permits an algorithm that simply stops with unresolved work.
To establish useful completion, add:

- A proved relation connecting finite facts to actual source constraints,
  boundary obligations and actual discovery, without dropping constraints.
- A clean-owner invariant stable under actual rewriting. Options are a common
  substitution/world parameter with a proved transport law for compile, or a
  canonical semantic representation with a proved interpretation relation.
  Neither is supplied merely by the one-way readback theorem.
- A service rule that re-establishes the selected clean-owner invariant and
  preserves other clean invariants, or a separately funded invalidation rule.
- A progress theorem for states whose exact active check fails. Such failure
  cannot simply reject a language program. The examples in section 1 show that
  it can occur after an otherwise valid representation step.
- A terminal characterization linking no actual step to every required owner
  being current and discovery being closed, including blocked owners.

To reuse least-fact/order results, prove actual discovery corresponds to a
monotone operator on the same fixed finite domain. Equal terminal public
solutions or canonical tables additionally needs semantic completeness or an
appropriate equivalence relation. One-way new-model-to-old-model readback
rules out newly admitted old-invalid models, but can still lose old solutions
through the fresh block, so it does not establish order independence.

## 5. Recommended next producer target

Before a solver Acc claim, choose a concrete actual-operation invariant that
excludes the three-owner cycle and mixed-coordinate trap, then prove it is
preserved by real fresh-block production and all actual rebase consumers.
A fixed, well-founded dependency order would be sufficient if it covers the
relevant type and row sources and is actually produced; an assumed arbitrary
rank would only relocate the obligation. Alternatively, a semantics-preserving
cycle treatment needs its own model contract and finite progress account.
The exact active checker is a useful diagnostic for this boundary, not its
termination proof.

## 6. Review of RankedTable245 added during this cycle

The new `GeneralPresenceRankedTable245` provides the sufficient representation
invariant mentioned above: all RHS sources lie strictly below their target's
fixed rank, each owner's targets have equal ranks, owner targets are disjoint,
and fresh targets stay within the former target set. Given fresh rankedness,
it preserves rankedness, uniformity and disjointness, and proves every next
owner passes the used-read table check. Its use of complete `typeSources`
correctly includes row reads. This excludes both section 1 examples, as needed.
No flaw was found in that theorem's stated scope by this source review.

Three producer/termination boundaries remain:

- Uniform ranks exclude even an acyclic dependency between two different
  targets owned by the same owner. This is sufficient for whole-block External,
  not a language-level necessity. Actual allocation/ownership design must
  justify it rather than reject legitimate constraints to enforce it.
- `TargetsWithin` permits dropping old targets but not adding reserved targets
  that were not already present as entry targets. Initial creation and any
  promotion that adds an entry therefore need separate producer obligations;
  fixed reserved identities alone do not establish this hypothesis.
- The rank is a dependency rank, not a decreasing transition rank. Even with
  one target, a sequence of fresh RHSs alternating bottom/top has no sources,
  satisfies every displayed rankedness condition, and can be rebased forever
  unless the actual scheduler disallows unpaid repeat service. Likewise,
  source-free syntax may grow arbitrarily under fresh production. These are
  permissive-interface examples, not actual solver traces.

Thus RankedTable245 closes a useful conditional *guard preservation* interface,
not the finite-work projection or the source-operation rank producer.
