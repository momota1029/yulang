# Cycle 104: checked grouped clauses and named ordinary input

Status: Draft implementation contract, 2026-11-11.

## Partial target

One finite, scope-resolved source boundary takes the existing grouped associated
clauses and named ordinary inequalities together. It computes the lossless role
package, structural occurrence program, extra-name allocation and initial State,
then runs actual mixed closure. Its independent judgment reads only the original
clauses and inequalities, not the checked program, allocated slots or final state.
The outer executable returns none for fragment checking failure and some Bool for
ordinary consistency after closure. It does not report role-resolution success.

For every finite source, core-well-formed env and associated-well-formed registry:
run = some true iff the source is valid for the existing one-placeholder checker
and there exists a single source type valuation satisfying every original
inequality and every independently derived scalar fact. Also characterize none
and some false exactly, and prove each checked run's per-valuation and evidence
correspondence. No checked program, successful check, State, extra-name domain,
model, fuel, consistency or role-success evidence is supplied at the outer entry.

The checker is CommonRoleSourceRoleObligations, which validates even bare role
clauses and retains one obligation per clause. Empty equation lists are not
silently erased for validation. Actual role discharge/final classification is
not part of the ordinary consistency result and remains explicitly separate.

## Authority and limits

Spec 6.3 supplies ordinary associated variables, equality flow and conjunction.
Existing x-oracle X13-X16 and C3-PARENT are source examples, not verification of
this adapter. No new Yulang2 execution or language semantics is claimed.
Names, the finite source clause list, named ordinary inequalities and registry
remain inputs. Parsing and full expression lowering, binder/invocation identity,
general ordinary entailment, dynamic child allocation, final four-way diagnosis
and dictionary observations remain open. The five B4 packages are unchanged.
Derives uses direct scalar pairs and reciprocal edges, not semantic knownness.
Unsupported scalar encodings can leave obligations unresolved even when ordinary
consistency is true. No role-satisfaction or whole-language rejection claim.


## Ordering and review

Whole-clause and ordinary-inequality membership equivalence implies identical
outer Option Bool outcomes. This covers reordering and duplicating either list,
without requiring equal allocation, slots, states or obligation multiplicities.
It does not cover changing the equation order within an individual clause.
Read-only review found no blocking mathematical mismatch in the independent
semantics, lossless checker, required well-formedness or outcome distinctions.
