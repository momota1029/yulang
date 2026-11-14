# Constructor coverage and the remaining variant-row materialization gap

Status: Draft repair guidance; source restriction, transfers, and counterexample proved in Lean.
Date: 2026-11-14. Scope: centered-19, baseline `1f5e40ea7`, `astra2/centered`.

The new `GeneralNominalCenteredHeadWFBoundary.boundary` strengthens Initial
with constructor interpretation coverage. Display/list, the alias fixture, and
the positional-default fixture meet it; the earlier uninterpreted-constructor
fixture does not. The twelve existing head-step bridge laws and the three
proved V6 target properties transfer to the same canonical executor.

Availability still fails at a well-formed, reachable, stable state: a closed
two-tag variant output has fully interpreted constructors but cannot be
translated by the existing output materializer. This is an implementation
coverage gap, not a new language question. Work stops at this checked
counterexample as requested. Default integration and merge-conflict reporting
remain open. No existing Step, refresh, Local, target, or executor is edited.

## The additive source contract

`GeneralNominalCenteredHeadWFSource.ConstructorUse catalogue interpretation k n`
requires a catalogue declaration for `k`, exactly `n` declared parameters, and
either a primitive interpretation with exactly the declared parameter layout,
or an invariant nominal interpretation with `n` type parameters.
`constructor_arity` and `constructor_interpreted` expose both obligations.

`PatternCovered` checks every application recursively in a general pattern.
`DeclarationCovered` checks heads, every unnamed where argument, every named
where-output RHS, and every explicit associated RHS. These are the source
patterns from which materialization requests are formed; coverage does not
assert that their normalized query translation is complete.
`DefaultsCovered` checks every role's declared default, including constructor
applications and their arities. `TermCovered` treats `Roles.Term.app` names as
resolved source constructor names; it does not decode `Pattern.encode`'s tags.
The role record already contains the positional-variable scope proof.

This uses the user's permitted **used-constructor** version of the contract.
The existing fixture catalogue returns a declaration for every natural number;
requiring interpretation of all its unused entries would reject those fixtures.
All role defaults are checked, rather than only defaults requested by the root.
Unreferenced catalogue entries themselves remain unrestricted.

The new Initial is precisely:

```text
HeadStepBoundary.Initial registry root state ∧
WFSource.Coverage registry state.core.erased.current.context.interpretation
```

The interpreter and catalogue are the existing source metadata, not a newly
chosen semantic assignment. The additional condition checks availability and
layout against that metadata. It does not provide a frontend producer or prove
that the separate `HeadDefaultSchemas.ConstructorMeaning` evaluator is coherent
with it. Those source-to-semantics connections remain explicit work.

`pattern_scoped`, `patterns_scoped`, and `declaration_scoped` connect the new
coverage to the old arity/scope checks. `declaration_reorders` and
`coverage_reorders` preserve coverage under the exact existing declaration and
registry reorderings. `HeadWFBoundary.reachable_coverage` carries coverage to
every reachable state's current interpretation using the existing Step
configuration invariant. No stronger refresh premise is added.

In `GeneralNominalCenteredHeadWFFixtures`, the concrete results are:

- `display_coverage`, `display_initial`: the ordinary registry containing the
  terminal int implementation, Display/list, and Wrap.
- `alias_coverage`, `alias_initial`: the existing two-child alias example's
  initial source. This does not assert that its old core trace is a head-step trace.
- `defaults_coverage`, `defaults_initial`: the existing positional-default
  source. Acceptance as a source does not claim installation by the frozen
  explicit-body readiness guard.
- `old_uninterpreted_not_covered`, `old_uninterpreted_not_initial`: the previous
  key-3 missing-interpretation fixture is excluded.

## Transfers and their exact scope

`HeadWFBoundary.initial_old` and `reachable_old` forget only the new coverage
conjunct. `local_iff` proves agreement of the complete V6 Local relation, and
`local_eq` packages it as relation equality. `local_total` and
`local_functional` follow. No candidate, output-conflict, or pending rule changes.

`GeneralNominalCenteredHeadWFTransfer.executor` and `frontiers` are aliases of
the existing canonical-registry definitions. The following are proved, with
only the original field premises restricted to the new reachability predicate:

| Theorem | Result |
| --- | --- |
| `progress` | Step accessibility at every checked reachable state |
| `stepModels` | every successor model restricts to its predecessor |
| `closure` | halted implies root and generated-demand stability |
| `execution`, `halted` | the existing executor runs under the original registry and terminates |
| `frontierLocal`, `localIdentity` | exact correspondence to the new boundary's V6 Local |
| `whereAccessible` | local Child accessibility, for every state |
| `treeExecution` | the executor tree equals the local resolver, given its ordinary exactness/accessibility premises |
| `dictionaryRefl` | dictionary equivalence is reflexive |
| `initialReorders` | reordered registries preserve the stronger Initial |
| `canonicalLocalOrder` | literal final V6 Local agreement for shared reachable inputs and reordered registries |

`canonicalLocalOrder` retains the full quantifiers:

```text
∀ r r', Checked r → Checked r' → Reorders r r' →
∀ s root, Reachable r root s → Reachable r' root s →
∀ d f, Local r (executor.run r s root).1 d f ↔
       Local r' (executor.run r' s root).1 d f
```

`exact`, `saturationTotal`, and `orderIndependent` prove the actual
`B4TargetV6.Exact`, `B4TargetV6.SaturationTotal`, and
`B4TargetV6.OrderIndependent` propositions for the new boundary and that same
executor. There is no additional simulation or confluence hypothesis.
No complete V6 Statement, dictionary evidence, or GeneratedChildren is claimed.

## A legal multi-tag row still cannot be materialized

The checked declaration has this shape; this is explanatory syntax, not a
claimed parser-to-state test:

```text
role P 'a
role Q:
    type out
impl P int:
    where Q(out = :{left int, right int})
// root demand: P int
```

[Spec §4.5 and §4.7b](../../spec/04-types.md) permit variant rows in annotations
and explicitly distinguish their separator from ordinary type union:
「variant の型の `|` は、型の union とは別物である」.
The final fixture uses the legal two-tag row, not an ordinary union annotation
(which §4.8 excludes). Both payloads use only constructor 2, interpreted as int
with arity zero. The reused source context also interprets its nominal list
constructor. No uninterpreted application is involved.

The pattern is `.join (.variant 0 (.app 2 [])) (.variant 1 (.app 2 []))`.
`HeadWFJoinSource.normalized_row` proves normalization retains it, and
`translated_join` proves the existing translator returns `.deferred` for that
whole row. `generated_unknown` then proves the emitted schema's `unknown = true`.
The translation's final catch-all case is the exact remaining gap.

The modules `GeneralNominalCenteredHeadWFJoinSource`, `...JoinLocal`, and
`...JoinCounterexample` certify the stronger Initial, reflexive reachability,
checkedness, a concrete model, full actual V6 selection, positive chosen-head
feasibility, feasible chosen class effects, and absence of output conflict.
Raw value support, choice compatibility, existing live-effect readiness, and
default-schema readiness also hold. The root has no named requests; the named
output belongs to its prospective child.

`HeadWFJoinCounterexample.stable` covers every constructor of the unchanged
Step: registration is complete, all sources are already known, descriptors
are point-closed, initial entailed equalities are already raw, there is only one
site to merge, and every installation Frame fails materialization. There is no
earlier administrative or refresh step to take. `not_committed` excludes the
already-installed escape, and `child_not_generated` proves the selected child
is absent (its role differs from the root's).

The premise-free results are `selected_stable_unavailable`,
`not_generatedChildren`, and `not_v6_selected_production`. The latter two negate,
respectively, the exact inherited V5 GeneratedChildren field and its corresponding
reachable/stable production law using actual V6 selected Local. `no_extension`
and `no_install` cover every current root Frame or root installation plan, not
just the exhibited plan. No extra assumption remains in the concrete obstruction.

This is a **source-to-materialization implementation gap** after constructor
well-formedness has been established. A further source contract demanding
translation completeness would exclude this legal row; it would describe a
supported fragment, not justify a language rejection or pending rule. Repair
requires lowering the complete output row into ordinary general-carrier
equations, or extending the output schema representation to express it. Merely
turning each alternative into a conjunctive singleton-head test would not
establish the intended row equation. No new owner decision is needed or proposed.

Default effect-ledger integration, general successor-model extension, and
merge-created conflict reporting remain unfinished under the requested stop
condition. The new source contract does not itself discharge those obligations.

## Validation and review

The `yulang-proofs` skill was used. No configured `prover` role is available;
the primary constructed the bounded proofs, with a separate read-only source
audit and fresh independent proof review. No prover agent ran. Independent
review checked the final variant-row fixture, source restriction, field
quantifiers, complete stability cases, and dependency limits.

Final commands, all with working directory `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadWFSource Yulang.GeneralNominalCenteredHeadWFBoundary Yulang.GeneralNominalCenteredHeadWFTransfer Yulang.GeneralNominalCenteredHeadWFFixtures Yulang.GeneralNominalCenteredHeadWFJoinSource Yulang.GeneralNominalCenteredHeadWFJoinLocal Yulang.GeneralNominalCenteredHeadWFJoinCounterexample > /tmp/centered19-modules.log 2>&1
exit 0
lake build --wfail > /tmp/centered19-build-wfail.log 2>&1
exit 0
lake build Yulang > /tmp/centered19-yulang.log 2>&1
exit 0
lake env lean Audit/GeneralNominalCenteredHeadWF.lean > /tmp/centered19-audit.log 2>&1
exit 0
```

[The new audit](../../lean/Audit/GeneralNominalCenteredHeadWF.lean) lists all
97 public theorem names, including the mutual scope lemmas. Its only logical
dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` and the baseline-prefix/import/dependency/proof-source checks
exit 0. Existing-file edits are exactly seven appended umbrella imports and
the appended INDEX entry. HEAD remains `1f5e40ea7` on `astra2/centered`.

Intermediate local checks returned exit 1 for proof elaboration or unused
arguments, corrected before the final checks. One Lake invocation from the
repository root returned exit 1 because the configuration is in `lean/`.
The final variant-row fixture and its principal dependencies also passed an
independent direct Lean check. No other test suite was needed for these
additive Lean and design-note changes.
