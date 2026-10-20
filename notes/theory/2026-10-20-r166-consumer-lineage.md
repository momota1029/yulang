# R166 backward consumer slice: ordinary forwarding and selector domains

Date: 2026-10-20. Status: **UNREVIEWED SOURCE/NATIVE EVIDENCE; original admission OPEN**.
Author: `/root/r165_native_admission_proof`; no coauthors or descendants.
Assignment `R166-NATIVE-CONSUMER-LINEAGE`, revision 1; baseline supplied and branch ref read directly:
`dbdf179986ac80608347dfc72c95d90b5ab9dfb7`.
Contract `tasks/agent-loop/sprints/native-consumer-lineage-and-runtime-completion-20261020-r166.md`,
SHA-256 `8f6515154a1f89038a5b7c4850c68c8e74967d8daab9972c932188fe9cfd8512`.

## 1. Original parent and actual application

Parent: computation-forwarding preservation §§1,6–7. Keep its shared assignment `xi=(nu,K,D)`,
original declarations/formals/providers/witnesses, ordered dependencies, arbitrary finite forwarding
chains, repeated calls and simultaneous entries. Neither accepted source behavior nor independent
F1/FK1/foreign-continuation obligations change. The required actual-provider admission remains
`mu(e_t)<=mu(e_n)<=mu(e_R)` and `mu(e_n)<=mu(e_t)`, with authentic per-use joins and current
residual/scoped lineage, not equality between template and copied endpoints.

R166 starts backward at the production Function AE/RE consumer. It establishes that ordinary
consumers and current original Name/body admission suppliers exist (§2), then identifies two concrete
limitations of the existing source-authentication interfaces (§3): the scoped Replay-demand selector
originates demands for calls of omitted callee formals, and the retained FormalConstruction supplier
likewise covers omitted formals. They do not supply the original explicit annotated forwarding case.
This result changes the appropriate evidence path: an omitted-callback demand selector cannot be
the only way to obtain the original parent's authentic ordinary provider/consumer tuple.

The remaining premise is the exact source-origin-to-actual-provider incidence in §4, followed by
R165's occurrence-specific transport/coverage and the separate replay residual law. No authentic
frozen ordinary tuple spanning that whole path was supplied by the fixed inputs or constructed in
this source inspection. That is a limit of this result, not evidence that ordinary consumers/fibers
are absent. No original premise is discharged, no source-qualified inference counterexample is
claimed, and all parent/A/B/native/runtime/production gates remain OPEN.

## 2. Backward consumer slice and grounded original suppliers

### Actual AE/RE consumers do not require a ScopedDemand

For a successful actual Function comparison `q` with actual positive provider `P` and negative demand
`D`, `lib::dispatch_live_item:12648–12720` derives its four child pairs from those exact term children.
Its AE and RE pairs are respectively `D.AE<=P.AE` and `P.RE<=D.RE`.
`candidate_step_function_dispatch:12800–12829` admits/enqueues each through
`candidate_function_port_admit`; the latter (`candidate_context:3405–3465`) retains

```text
FunctionPort { child: ae, parent: q, field: ArgumentEffect, operation: Swap }
FunctionPort { child: re, parent: q, field: ResultEffect,   operation: Preserve }
```

The inherited context is `post_check_context(q)`, swapped for AE and preserved for RE, with the
child-local source wrapper prefixed in the prescribed order. Its sources are q's exact source set.
When no scoped demand exists, the constructor still admits these ordinary children. When one does,
it checks the negative root and constructs the specified stamp/protect transformer before clearing
the demand. Thus absence from `ReplayDemandRow` is not absence of FunctionPort consumers.

The live typed drain installs q's actual item/relation, performs Transport and Context before
Dispatch, and installs each Function child through its pending admission/enqueue states
(`lib:12344–12449,12800–12829`). Equality transport keeps the original relation as a Derived parent;
it does not identify q with a different relation merely because endpoints now coincide. This is a
source fact about any actual successful dispatch, not a claim that a desired numeric q was observed.

Backward from q, a `Dependency::Replay` retains the exact ordered lower/upper input relations and
BoundKeys (`candidate_context:3808–3865`). Its lower input is the provider-side fiber, its upper input
the demand-side fiber. A child can have multiple dependencies under relation interning; selecting
one by endpoint or count is not authenticating the actual constructor occurrence. Bound admissions
retain `relation`, `cause`, imported antecedent where present, and physical emissions/readback
(`candidate_context:513–537,733–779`; `candidate_extrusion:501–674`). These are relevant backward
suppliers. Their coverage flags deliberately preserve missing ordinary-seed/processing antecedents;
a retained record with such flags does not silently prove full original-source association.

### Original annotated Name/body admissions have current source owners

The extra local source dependencies below were explicitly admitted read-only by Luna during R166.
They ground source admissions and selector applicability, not a broader source census.

`candidate_source:869–879` registers an explicitly effect-annotated formal as Computation with its
original parameter/owner/lambda. `initialize_candidate_source_levels:1596–1620` allocates its actual
entry effect `e_t` at that original formal's level and retains it in that registration.
For a resolved Name of the same formal, `candidate_source:1294–1305,1736–1740` emits
FormalNameEffect using that exact registration and the Name's actual effect component `e_n`.
`candidate_effect::candidate_formal_effect_equal:1439–1450` admits both actual directions at that
Name's slots 1 and 2. This is original formal identity, not a reconstruction from equal row shapes.

`lib::admit_lambda_fact:11322–11495` selects that registered Computation entry as Function AE, omits
Value-entry slot 3, allocates the provider RE `e_R`, and emits the actual body-effect<=RE constraint
at the Lambda's slot 4. For the parent's direct Name body its body effect is precisely `e_n` from
the recipe. It constructs the positive Function with that AE/RE and emits it at Lambda slot 2.
Consequently the current original-template supplier is grounded:

```text
Name(t), slot 1: e_t <= e_n     Name(t), slot 2: e_n <= e_t
Lambda, slot 4: e_n <= e_R     Lambda, slot 2: actual positive Function <= root
```

Each constraint enters its own actual source occurrence/typed drain. The resulting `Origin` records
retain occurrence/relation even when `formal` is None (`candidate_context:3271–3341`). None of these
facts identifies the template rows with a later provider copy. Original Int value constraints are
not replaced by an Int leaf, and concrete permission families do not cap incoming entry E
(`candidate_effect:1453–1465`).

The current Apply owner is also explicit. `shadow_apply::admit_candidate_fact:1763–1927` checks the
source input/recipe, builds the negative demand using the actual argument and its entire argument
effect, admits callee<=demand at checking slot 0, then admits actual invocation RE<=Apply output
effect at slot 2. These supply the parent implication's outside links once the positive provider's
authentic mapped Name/body constraints are established. No run or successful whole solve is inferred
from reading these constructors.

## 3. Constructed selector-domain limitation

### ReplayDemandRow selects an omitted-callee construction

1. `candidate_source:929–941` records formal-name identity for resolved parameter Names.
2. `ApplySourceInput.formal_name` is populated from **the callee**, not the argument
   (`candidate_source:1422–1431`). A whole current Computation formal passed as argument does not
   thereby make this field Some. A direct resolved module/local declaration Name used as callee
   has no parameter-formal entry in this table.
3. `shadow_apply:1840–1855` constructs DirectionalIntroduction only from that callee formal's
   original lambda in `omitted_formals`. That map is populated only when the original parameter
   annotation is absent (`candidate_source:1014–1022`). Explicit `[S]Int` formals do not enter it.
4. `candidate_context_seed:3294–3306` originates `ScopedDemand { original_call: c, ... }` only at
   a call's checking slot 0 when that call has this introduction, and only in scoped mode.
5. `replay_demand_rows:2788–2800` selects a Replay dependency only when its child has a demand;
   its call index is that demand's `original_call`. The public diagnostic selector then invokes
   `authenticate_demand_transport` (`shadow_apply:321–335`).

For an original forwarding occurrence that calls a declared function G and passes the current
annotated Computation formal t as its whole argument, step 2 supplies no formal-callee introduction.
For a call whose callee itself is an explicitly annotated formal, step 3 also supplies none. These
are source-constructor facts, not missing-fixture guesses. In ordinary `solve`, scoped mode is false
(`shadow_apply:274–275`) and this scoped selector is separately inapplicable.

The absence of a call's own original demand seed persists along the inspected transport constructors:
FreshUse remaps scopes/inputs/root/use while retaining `original_call`; ordinary transport rewrites
only a matching demand root; Replay retains the upper demand and rejects a demanded lower;
FunctionPort consumes/clears the demand. None creates a new original call identity
(`candidate_scheme:1773–1799`; `candidate_context:2766–2779,3389–3395,3443–3453,3844–3849`). The only
production `ScopedDemand` struct constructor in the inspected solver source is the seed above.
This induction excludes manufacturing that missing call-c selector record by copying a different
call's demand. It does not exclude ordinary relations, receivers, effects or consumer execution.

Even inside its supported domain, `authenticate_demand_transport_observed:412–601` authenticates
the negative demand's exact FreshUse route and then looks for both positive and negative Function
nodes in that same graph/map (`:542–568`). A positive provider with a separate actual route needs
its own retaining incidence; failure of this same-graph condition is not an inference counterexample.
Its supported zero-step Replay-upper/consumer cases are not evidence for arbitrary rewritten spines.

### FormalConstruction is not the explicit Computation-formal supplier

`lib:11461–11475` retains `FormalConstruction` only after lookup in `omitted_formals` and an exact
raw Function-domain check. The parent has explicitly annotated Computation formals, so those provider
constructions do not obtain this optional handle from that branch. Their ordinary source Origin is
still retained. `candidate_formal_argument_incidence:361–438` is an inert, bounded Argument-port
inspection through one captured bound and optional Name handoff; it searches precisely that optional
handle and expressly excludes earlier extrusion/derived routes. It neither authenticates the
original parent's arbitrary AE/RE supplier nor proves such a supplier absent.

These two interface limits explain why demanding more successful queries from these selectors
would not establish the original witness/consumer pair. Adding an artificial annotation restriction
or using an omitted-formal sibling would change the parent and is not an admissible repair.

## 4. Exact remaining premise and minimal next evidence

**R166-ORDINARY-PROVIDER-INCIDENCE-1.** Starting with the actual AE/RE FunctionPort constructor event
and its actual q, retain the selected ordered Replay/Derived/Transport incidence to the exact
positive-provider admission. Link that source admission to the original Lambda recipe/registration,
Name slots 1/2 and body slot 4, and to the provider's own authentic per-use maps. Carry all required
original witnesses through the actual capture raw key/shared anchor and every extrusion,
qualifying merge/recapture and Replay to this q, preserving dependency order and current
residual/scoped payload. An independently scoped demand route cannot replace the provider route.

First owning seam: `candidate_context::{candidate_function_port_admit,candidate_context_begin_replay,
candidate_context_bound_for}` plus the actual `BoundAdmission`/`BoundEmission` cause.
Source supplier: `lib::admit_lambda_fact`, its `LambdaRecipe.formal_registration`,
`candidate_source::{FormalNameEffect,initialize_candidate_source_levels}`.
Per-use/transport supplier: `candidate_scheme` retained provider route and
`candidate_intrusion` occurrence-associated parents; then R165-CAPTURE-CONSUMER-1 applies.

The exact ordinary tuple is not reconstructed here: q's relation/key alone does not select a unique
original provider occurrence or source admission when relations are interned and several dependency
routes are retained. The current inert evidence explicitly leaves ordinary seed authentication and
processing antecedents uncovered; an optional omitted-formal handle cannot fill those cases.
This is the missing supplied association and proof, not a claim that no association can be recovered
by a richer constructor induction. R70 ENTRY-WF and R71's occurrence-specific canonical/raw lineage
premises are not established by this backward slice.

Minimal prospective evidence TODO: an exact ordinary FunctionPort-centered observation or
source-construction certificate linking **q, field-child, ordered actual producer dependency,
full provider BoundKey/admission/emission/cause, original lambda/registration/Name-body occurrences,
provider route-use identity/maps and current residual/scoped state**. Preserve multiple actual
routes instead of demanding accidental uniqueness. Reuse existing retained records where possible;
do not alter inference or authorize a semantic consumer with this inert evidence. This is a TODO
for Luna's next bounded grant, not permission to instrument or execute during R166.

Falsifier: a production-reachable accepted original history with an authentic required provider
witness whose actual selected consumer cannot receive its lineage along any justified retained
route. A missing ScopedDemand/FormalConstruction handle, duplicate relation ID, count, sibling route
or endpoint-only model is insufficient. A complete source-constructor induction for the original
scope could instead discharge the premise without adding observation code.

Replay residual correspondence stays separate: FunctionPort uses the post-check residual, while
Replay builds from immutable parent contexts and may need original filters on a new opposite product.
No equivalence, bug or counterexample follows solely from that difference. No local frame theorem
discharges F1/FK1 or foreign-continuation quantifiers.

## 5. Pins, checks, authorship and stop

R165 restoration is reused only as its actual captured-fiber supplier, not restated as a new theorem.
R70 remains conditional under successful-call/ENTRY-WF premises. R71's forward preservation is not
used as a converse. The original template and conditional native implication retain their premises;
source owners above ground their current supplier, not all-source closure. R50/withdrawn bypasses
are not restored.

```text
parent              d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
R70 result          648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7
R71 result          620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e
R165 result         ac8f211679cb8c44d7834069d821e0a774f83fdc379845ca9ad110eb3b14b9aa
R165 closeout       7c522f0b4f4851ca620f75889c08e78cbe6d63752fb8140492fd66b022506f82
candidate_scheme    2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
candidate_extrusion 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332
candidate_intrusion 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
candidate_context   93ff11f005c9e29e007d2a21479779dd14ff462a41da9c937a0e6a48fc1603be
solver lib          c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
candidate_source    cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
candidate_effect    c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1
shadow_apply        838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
```

Checks: exact SHA-256 reads, direct branch-ref read, source/authority inspection and backward/forward
constructor reasoning. No Git command, tests, builds, probes, instrumentation, compiler/runtime/Y2/Y3
execution, network, external/user contact, descendants, generated or scratch paths. Only the two
leased R166 outputs were written. Requested model/effort UNKNOWN/UNKNOWN; observed UNKNOWN/UNKNOWN.
Fresh grant 900 seconds, started by live receipt at 13:52:30 UTC; no carryover or extension, Astra 0.
The exact missing association is the stop condition; no active-time reclaim is requested.

Frozen revision 1 for fresh independent review. No author self-certification. **STOPPED, writes
stopped with the inbox handoff; no descendants/background processes or additional leases.**
