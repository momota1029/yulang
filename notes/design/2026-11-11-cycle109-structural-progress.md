# Cycle109: structural evidence progress under actual ordinary extensions

Status: Draft proof plan, 2026-11-11. B4 termination component, no new language rule.

The recovered structural detector deliberately requires one distinct syntactic
payload. Unlike scalar evidence, two different structural payloads can have the
same Common meaning. Adding the paired bounds for `int | int` after the bounds
for `int` is consistent, but changes the detector from `some int` to `none`.
Therefore the older one-change-per-variable argument and syntactic fusion do
not extend. Do not silently assume them or pick one payload by declaration order.

For every two finite atom lists A and B with A included in B, prove monotonicity
of a three-phase evidence measure: no payload costs 2, one distinct payload costs
1, multiple payloads cost 0. Each actual detector change strictly reduces it.
For every source Form and interval Goal, sum this measure over original variable
occurrences. For any finite inclusive state sequence, materialized goal changes
are at most twice the number of original variable occurrences. No consistency,
model, payload-size, unique-impl or successful-role premise is required.

Then connect the result to cumulative states actually computed from additive
ordinary batches, and to complete diagnostic-tree replay. This does not prove
that the batch stream itself terminates, nor bound the size of a future payload.
State plateaus cannot stop processing. Failed diagnostics are retained.

Yulang2 cross-check: read work/dots-audit y2-claims-role-boundaries-cycle-2.md,
ROLE-MORE-001/002 and 003/005. Candidate order must not choose a winner; old
where handling differs from spec6.3. The measure is an executable implementation
accounting property, not an adopted Yulang2 language classification. The existing
Common union semantics supplies the equivalent-syntax regression. No new Y2
execution is claimed. All five global B4 bridges remain open.

## Second subgoal: computed child domain and lossless replay

First progress result passed and was published at 421c0df28. Next compute a finite
palette directly from an ordinary atom envelope: each source occurrence may
remain a variable or use a payload with paired bounds in that envelope. For all
substates, the palette covers materialization and the Paterson closure covers
every recursively generated child. This envelope is the final cumulative state
of the submitted finite batches, computed internally, not a supplied work list.
The bound applies to this finite job; future evidence outside it may enlarge it.

Reuse complete diagnostic trees only on literal materialized-goal equality;
refresh ordinary graphs on every occurrence. Prove exact snapshots, lossless
fresh graphs, and rebuilds bounded by one plus twice original variable count.
The runner validates actual cumulative states using the existing ordinary solver.
It does not generate the finite batch stream or prove general saturation.

## Third subgoal: generated structural evidence, rather than direct seed pairs

The domain/replay modules compile. The next bridge applies the existing finite
structural decomposition/transitivity closure to each internally computed
ordinary state before materialization. Paired bounds reached through source
variable links become usable without caller-provided propagated evidence.
Characterize detection by the independent seed/split/trans derivation, preserve
every original model, and lift monotonicity, change budgets and child domains
through normalization. The closure is a terminating existing finite Horn
implementation, not arbitrary semantic entailment. Its State grammar permits
paired int/pair upper bounds; join/tick bounds remain supported by the raw graph
adapter but are not silently promoted to the restricted checked State grammar.

## Fourth subgoal: internally generated finite structural saturation trace

The first three pieces are published at 9f25e9248. Remove the caller's finite
batch sequence for the existing ordinary seed/split/trans closure: instrument
the actual FiniteHorn.firstFresh iteration, with capacity computed from its
syntax-derived carrier, and expose its fresh atoms in actual discovery order.
Accumulate these atoms into ordinary snapshots and feed the proven structural
replay. Prove final membership iff independent Derives, every snapshot's models
exactly equal the original state models, terminal closure, and computed bounds
for the full driver. The actual ordinary solver gates the original State;
semantics preservation justifies all subsequent generated snapshots.

This is a complete driver for the existing finite ordinary rules only. It does
not feed role candidate constraints back into ordinary closure, add new source
names, or replace the uncompleted general B4 mixed-saturation driver.
