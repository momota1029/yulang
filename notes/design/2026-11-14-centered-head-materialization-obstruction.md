# Centered V6: a stable selected source without materialization

Status: Draft repair proposal; the counterexample is checked in Lean.
Date: 2026-11-14. Scope: centered-18, baseline `4690c5995`, `astra2/centered`.

The requested general selected-to-installable implication is false for the
current head-step boundary, even with positive chosen-head feasibility,
`LiveEffectsReady`, empty raw support, and no output conflict. A checked ground
initial state is already stable, selects a parent with one child, and cannot
generate that child. This meets the user's explicit counterexample stop
condition. Default-ledger integration and merge-conflict reporting stop here;
neither is claimed complete. Refresh and all previous definitions are unchanged.

## The source and the failed bridge

The declaration-level example has the following shape (schematic Yulang;
the executable fixture is the Lean declaration, not a parser test):

```text
role P 'a
role Q:
    type out
impl P int:
    where Q(out = Opaque)
// demand: P int
```

`P` is role 0 with one unnamed argument. `Q` is role 1 with no unnamed
arguments and declared named output 0. The only visible implementation is
declaration 37; its child clause is 42 and its child output equation is 43.
The head is `.app 2 []`, while `Opaque` is `.app 3 []`.
The declaration checks all existing signature, constructor-scope, output-scope,
and descent conditions. The unnamed head has size 1 and the child's unnamed
argument list has size 0. The named output does not contribute to that count.

The context reuses `GeneralNominalCenteredTerminalForkSource.context (some false)`.
Its three sources have known heads: source 0 is a nominal list with point
argument `(1,1)`; sources 1 and 2 are `int`. Root 100 is `P` at `(1,1)`, with
no output requests. Its center is therefore source 1. The separating assignment
maps source 0 to `list int` and all other names to `int`.

The constructor catalogue declares key 3 with arity zero. The interpretation
supplies scalar key 2 and nominal key 0, but no interpretation for key 3.
`InitialSource.metadata` only checks the compatibility of entries that are
present. It does not require coverage of every constructor used by emitted
outputs. Consequently this is a literal `InitialSource`, a ground point-root
`boundary.Initial`, and a reachable state by the reflexive trace.
It is not asserted to be produced by a completed source elaborator: no such
producer with interpretation completeness has been established by these results.

The proof isolates the precise failure:

```text
translate snapshot.constructors context.interpretation (.app 3 [])
  = .deferred (.app 3 [])
(generated registry context root declaration declaration_checked [(1,1)]).unknown
  = true
```

`HeadCandidates.Prepared` checks the parent head and succeeds. The chosen class
has no requests, so both the existing explicit class equations and the proposed
default-schema equations hold. Installation separately requires the complete
emitted schema's `unknown = false`. That guard fails for every current Frame.
No default is used in this example, so wiring the existing default evaluator
into class effects alone cannot supply the missing child materialization fact.

## Exact certified statements

The new modules share the prefix `GeneralNominalCenteredHeadStepMaterialization`.
All public theorem names are listed in the accompanying
[audit](../../lean/Audit/GeneralNominalCenteredHeadStepMaterialization.lean).

| Module suffix | Principal results |
| --- | --- |
| `Source` | `checked`, `source`, `ground`, `initial_source`, `reachable`, `inhabited`, `prepared`, `unsupported_constructor`, `generated_unknown` |
| `Local` | `unique`, `frame`, `effects_ready`, `live_effects_ready`, `default_schema_ready`, `default_schema_equations`, `choice_compatible`, `positive_baseline`, `common_effects`, `no_output_conflict`, `selected`, `value_support` |
| `Counterexample` | `frame_unknown`, `no_extension`, `no_install`, `stable`, `halted`, `child_not_generated`, `not_committed`, `selected_stable_unavailable`, `not_generatedChildren`, `not_v6_selected_production` |

`selected_stable_unavailable` has no hypotheses. It packages boundary
checkedness, reachability, stability, actual V6 selection, the positive baseline,
absence of conflict and commitment, absence of every root installation, and
absence of every Step. The root is the only generated demand. Stability checks
all administrative cases as well as refresh, installation, and merge:
all sources are already known; descriptors are point-closed; every entailed
initial equality is already raw; the root is registered; and there is only one
site. This is not merely failure of a chosen plan or a nonterminal snapshot.

`no_extension` is universal over every plan with a current Frame at the root.
`not_generatedChildren` negates exactly
`B4SkeletonV5.GeneratedChildren (B4TargetV6.prior (HeadStepBoundary.boundary roles))`.
Since that inherited field uses `SafeKnown` and `Unique`, the separate
`not_v6_selected_production` also negates the corresponding reachable/stable
production law with actual V6 `Local = selected` as its premise. The missing
child has role 1, whereas the root has role 0, so it cannot be generated merely
by the reflexive root rule. Its edge is absent, and the packet is not committed.

These concrete negative theorems have no undischarged assumptions.
Helper statements retain exactly their displayed Frame/focus premises;
`default_schema_equations` quantifies over any constructor meaning because its
request list is empty. It does not certify source faithfulness of that meaning.

## Repair boundary and owner intent

[Spec §6.1](../../spec/06-roles.md) permits default omission:
「default があれば省略できる」. §6.3 says associated equations use ordinary
constraints and that incompatible accumulated constraints cause an error:
「それまでに積まれた制約と合わなければ、その時点で型エラーになる」.
The current fixture has a feasible chosen class and no such conflict.
An omitted interpretation is an implementation gap, not evidence for rejecting
the program or filtering its head candidate.

The smallest missing producer obligation is **source-faithful interpretation
coverage for every pattern that materialization consumes**, including named
child outputs. Constructor scope alone is insufficient. A future additive
source contract could state that every elaborated constructor has its actual
general-carrier meaning and that translating every emitted schema is complete.
That contract needs a producer and preservation proof; assuming it locally
would not discharge `Extension` for the existing boundary.

Prefer implementing that elaboration/translation connection, shared by explicit
schemas and role defaults, then form an additive boundary whose Initial uses
the resulting source data. If the current interpretation is intentionally
partial even for legal concrete outputs, materialization itself needs a
successor that represents their ordinary equations. Do not turn an absent
interpreter entry into a new pending rule, arbitrarily mark every constructor
invariant, or decode default `Roles.Term` names through `Pattern.encode`'s
unrelated counting tags. No new language decision is made here.

The existing 17th-turn canonical-order proof remains valid for its unchanged
boundary. It does not supply child production. Default-aware operational
integration, general common successor models, and merge-created conflict
reporting remain open. No claim about a future corrected elaborator or
default-aware successor Step is refuted by this example.

## Validation

The `yulang-proofs` skill was used. No configured `prover` role is available,
so the primary constructed this bounded derivation. Independent review confirmed
the exact source/reachability premises, all stability cases, and the distinction
between this formal InitialSource and a future complete source elaborator.
No prover agent ran.

Final checks, all with working directory `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadStepMaterializationSource Yulang.GeneralNominalCenteredHeadStepMaterializationLocal Yulang.GeneralNominalCenteredHeadStepMaterializationCounterexample
exit 0
lake build --wfail
exit 0
lake build Yulang > /tmp/centered18-yulang-build.log 2>&1
exit 0
lake env lean Audit/GeneralNominalCenteredHeadStepMaterialization.lean > /tmp/centered18-materialization-audit.log 2>&1
exit 0
```

The audit covers all 54 public theorems and uses only `propext`,
`Classical.choice`, and `Quot.sound`. `git diff --check` and the scripted
baseline-prefix, import, proof-source, and dependency checks exit 0. Existing
tracked changes consist only of appended imports and the appended INDEX entry.
HEAD remains `4690c5995` on `astra2/centered`; no refs were changed.
Intermediate single-file elaboration checks returned exit 1 for local proof
errors, all corrected before these final checks. No target or operational
definition was changed, and no general availability theorem is certified.
