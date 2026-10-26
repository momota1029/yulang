# Goal-indexed admission for original finite Function checking

Status: constructed, module-checked, and fully origin-audited; fresh independent
review is pending in the paired handoff. This closes the
current-goal admission mismatch identified by the original source checking
packet. It does not establish complete original inference soundness.

Authority: [SG §3.2(4)](2026-10-08-source-generalize-definition-and-proof.md#32-checking-and-actual-elaboration-rules),
with the actual callable, complete original domain and joint observation
semantics of the accepted OriginalSourceInterpretation and Environment modules.
The preceding limitation is recorded in
[original source checking](2026-10-26-original-source-checking.md).

Implementation: `YulangClosure.OriginalCheckingAdmission`, using the minimally
corrected `OriginalSourceGeneration`, `OriginalSourceEnvironment`, and
`OriginalSourceChecking` interfaces. The three existing modules were frozen
separately after their complete core audit; their exact hashes and previous-root
inventory are in the core-only handoff.

## 1. The original missing premise

Complete Function checking from A to F requires a finite proof of
`D_F ⊆ D_A` and, for each challenge in D_F, a finite proof transporting the
whole source observation to the checked observation. Logical composition may
introduce intermediate descriptors at the same actual source occurrence.

The old `Kernel.admitted environment binder candidate` had no current CheckGoal.
The concrete Environment interpreted its invocation domain at the binder's
original descriptor slot. Its accepted Function application theorem therefore
needed an explicit `targetReadback` equation equating that slot with the current
checked upper descriptor. That equation is valid at the initial App goal but
cannot be assumed for every composition intermediate.

Changing the source binder domain would affect Lambda, source forall/exists,
execution, and Shared rules. Enlarging every source domain, requiring equality
of all intermediate descriptors, or retaining only challenges already admitted
by the original binder would change the original statement. None is used here.

## 2. Separate source and checking admission

`OriginalSource.Kernel.checkingAdmitted` has the type

```lean
Environment Value → CheckGoal → Binder → ScopedValue Value → Prop
```

The only checking grammar use is the observation premise of
`Checking.function`, at that constructor's enclosing goal. Its default is the
legacy source admission, ignoring the goal. Existing source-rule constructors
and Satisfies clauses continue to use `Kernel.admitted` with their original
arguments. Source builders, generated formulas, all raw keys and runtime
payloads remain byte-identical.

`default_checking_admission` proves the backward-compatible omitted-field
construction. `admission_update_keeps_checking` records an important update
fact: replacing admitted does not recompute an already stored default.
Accordingly, the accepted Environment admissionKernel and functionKernel
explicitly assign both fields to their legacy relation. Their old conditional
Function theorem remains valid.

The new wrapper order is explicit:

1. The accepted functionKernel installs the original source admission and
   authentic raw Function incidence.
2. goalAdmissionKernel replaces only checkingAdmitted with GoalAdmitted.
3. registeredKernel installs finite registered proof schemas and preserves
   both final admission fields.

`function_kernel_admissions` and `registered_kernel_admissions` prove the two
final projections. The latter also proves that the registered FunctionShape
uses this exact goal-indexed predicate. Calling a legacy wrapper after step 2
would deliberately restore legacy checking admission and is not the final
composition used here.

All seven existing Kernel record-update sites are accounted for. The literal,
Name and folded literal/Name atom updates preserve both admission fields;
the two Environment admission-changing wrappers explicitly reset both; the
registered Checking wrapper preserves both. The corresponding conservation
theorems are in the new module. This is conservation of source admission
telescopes, not blanket equivalence of source judgments whose local checking
semantics is intentionally corrected.

## 3. Concrete current-goal admission

GoalDataAdmitted handles a raw invocation using the same CallOwner's actual
callable value/root and the descriptor at `goal.upper`. It checks the complete
original CheckedDomain before provider acceptance or body behavior:

```text
original invocation kind
same actual callable value
same actual callable root
CheckedDomain(raw challenge at current goal.upper)
```

Its environment wrapper retains the original candidate-parent scope and the
deterministic heterogeneous decoder. Every non-invocation payload delegates to
the unchanged original DataAdmitted relation. No observation-safety test,
provider filter, stored-strategy lookup, descriptor equality, arity encoding or
new runtime field is added.

The two admission directions are constructed:

- `goal_challenge_supplies_admission` encodes every complete original admitted
  challenge of `state.goalRow binder goal` at its actual occurrence, given its
  original view/event registration equations.
- `goal_admission_recovers_challenge` recovers the exact raw invocation,
  actual callable/root and full target-domain proof from an admitted candidate.
- `goal_invocation_has_active` constructs the decoded child state and its
  actual active CallInput. It never turns an inactive observation identity into
  an observation-safety result.

`goal_admission_aligned_legacy` establishes equivalence with old admission only
under the explicit descriptor alignment. `initial_goal_admission_legacy`
specializes it to the original binder descriptor endpoint. There is no general
goal-admitted-to-legacy-admitted conversion.

### Original source and native incidences

`source_app_admission_recovery` obtains the actual unannotated App checking
premise from sourceRules and proves initial-goal admission recovery for that
premise. It preserves the ViewLogic binder and the lower endpoint
`callee.returnedValue`; the App result is a different endpoint. This source
incidence theorem is explicitly about the unannotated App clause, not an
erasure of the separate annotation Boundary rule.

`goal_app_callable` and `goal_lambda_callable` use Root.withSource's actual
sourceCallOwners registry. They show that any intermediate target keeps the
App's returned callee or the Lambda's own final-root callable respectively.
`goal_invocation_captures_subject` connects the admitted payload to the active
runtime input at this same registered subject.

`native_received_supplies_goal_admission` composes the actual Received packet,
the original native Receipt insertion theorem, and the new goal-admission
encoding. It retains the owned view token and all raw invocation fields. The
remaining view/event equalities are the original semantic field readback,
not a consequence of token equality alone or a promised safety certificate.

## 4. Descriptor-independent actual input

A Challenge contains its checked descriptor in its row index; CallInput and
the raw Invocation do not contain that descriptor. This distinction is proved
at the full tuple:

- `encode_retarget` preserves the complete raw Invocation and native view token.
- `decode_encode_input` recovers the exact CallInput even if the runtime decoder
  decorates the intermediate challenge with a different descriptor.
- `encoded_scope_retarget` preserves the actual scoped payload.
- `encoded_event_path_retarget` preserves the actual event path, including its
  original parent path, binder and occurrence.

The decoder may therefore retain its existing binder-descriptor implementation
for runtime.active. Only the descriptor-free input survives that computation.
No runtime or event-identity representation was changed.

This preservation does **not** imply that descriptor-indexed checkedIncidences
or view/event registration premises survive arbitrary retargeting. Every new
Function theorem quantifies its viewReadback and eventReadback laws over
`Challenge (state.goalRow binder goal)` and that challenge's own
`inputs.checkedIncidences`. It does not reuse a binder-row law by silently
transporting incidence.

## 5. Observation transport and the Function constructor

`goal_observation_child_transport` starts with a challenge in the current
goal's D. It constructs the exact candidate, obtains the recursive observation
meaning in its decoded child state, and identifies the active input using the
input round trip. The endpoint equation `observation.upper = goal.upper`
comes from the actual finite Function shape. No equation between the original
binder descriptor and goal.upper is required.

The lemma transports the entire positive observation predicate at the same
raw observation. It does not infer observation preservation from equal runtime
inputs alone; the recursive observation proof supplies that semantic action.

`goal_function_at` combines this action with the recursively obtained domain
meaning and actual target guard/capture premises through the accepted
same_provider_function_check theorem. It preserves every actual provider
decomposition and complete raw execution observation.

`goal_function_checking_constructor` constructs the actual finite
Checking.function node with its two recursively checked children, and returns
the corresponding current-event FunctionAt. The explicit local semantic
induction hypotheses are discharged in the registered application below.

### Application of actual finite Checking proofs

The generic registered Checking induction is still the actual mutual
Checking.rec, including its list motive and every admitted observation child.
FunctionLeaves now retain the enclosing goal and its exact checking admission.
The primitive, structural, union cases, identity, composition and boundary
constructors are not replaced by new safety predicates.

`goal_function_children_at_meaning` applies this finite induction to both
recursive children. It derives DomainMeaning, constructs the active invocation
for each goal-admitted observation child, and applies observation_action.
Independent target guard/capture consequences are obtained from finite
registered Proof code, with no arbitrary whole-goal semantic-inclusion leaf.

`checked_current_function_from_meaning` starts with completed source Meaning,
unfolds its actual Function core using the source classification, and applies
those recursively checked children. Its conclusion is target FunctionAt at the
current event. The source actual provider/value/root remain the same.

## 6. Nonconstant domains and the missing-challenge direction

The Discriminator namespace is a concrete finite test of the interface. It is
not offered as a complete interpretation of Yulang's original primitive
declarations. Descriptor, interface and carrier are Bool; all unrelated input
fields are explicit. The source-owned registry contains an actual raw App with
a Lambda callee. The App's result value differs from its returned callee value.

The independent checked inlet relation is

```text
checkedInlet(d) = d
carrierAccepted(i, c) iff i = false or c = false
```

Thus both domains are nonempty, with

```text
D(false) = {false, true}
D(true)  = {false}
```

The module proves exact characterizations of goal and legacy admission, then
both discriminating directions:

| Original binder descriptor | Current target | Carrier | Legacy admission | Goal admission |
| --- | --- | --- | --- | --- |
| false | true | true | admitted | rejected |
| true | false | true | rejected | admitted |
| either | either | false | admitted | admitted |

The second row matters for a source-to-intermediate-to-final derivation whose
final domain is narrower than the intermediate domain. The old binder-indexed
observation telescope would omit that intermediate challenge. The corrected
one includes it. No general goal-to-legacy conversion is used.

The fixture separately proves that source and target descriptors differ in
both directions, while encoded invocations and actual event keys are equal
under target changes. These are kernel-checked proofs using ordinary decide
only for closed Boolean inequality; no native evaluation axiom is used.

## 7. Exact remaining boundary

The original target-domain mismatch in the finite current-event Function
application is closed. The new field is exercised by the actual mutual finite
Checking induction, raw source ownership, native receipt construction and a
nonconstant bidirectional admission discriminator.

The following larger obligations remain separate:

- Original declaration/native readback must construct every primitive and
  structural registered proof required by the full source grammar. The
  registered-proof kernel is not asserted to be the complete original kernel.
- The actual source registry must supply view/event and guard/capture readback
  at every required occurrence. The current theorem keeps these exact local
  obligations explicit.
- A hereditary FunctionShape requires registration and child-proof action at
  all original compatible future events. In particular, the existing
  `OriginalSourceChecking.stateClause` reads each value event probe, whereas
  its domain branch guards the input by equality with the decoded current
  event. The next concrete owner is the original source/event registration
  connecting those child readbacks to the same later event, together with
  that event's actual view/receipt, guard and capture incidences. A current-event
  FunctionAt result alone does not establish all-future target value membership.
- Genuine recursive L4 and original joint recursive introduction remain open;
  neither rejected provisional-candidate checking-closure argument is used.
- Native success-to-satisfaction and the full original inference theorem are
  not consequences of this admission repair alone.

## 8. Verification record

The paired handoff records exact source hashes, toolchain, commands, complete
origin/type/axiom inventories, retained failed attempts, resource bounds and
independent-review status. The initial input manifest and every actual check
snapshot are retained from check1. The three unchanged core origins were fully
audited once at their frozen checkpoint; the new module receives its own full
origin audit. Shared/default integration and Git remain primary-owned.

The final new-module build is check9; the complete origin census is check10.
It covers 90 originating declarations, 65 theorem constants, and all 45 authored
theorem roots, including private/generated declarations. Actual standard axiom
union is `propext`, `Quot.sound`, `Classical.choice`; no project or unexpected
axiom was found. Core check3 separately covered 2399 declarations, 943 theorem
constants and all 152 previous authored roots. The primary reports that exact
core checkpoint published as `4c5fff3b2addbbea61a110865cb9273d10c9f97d`;
its three mathematical source hashes remain unchanged.
