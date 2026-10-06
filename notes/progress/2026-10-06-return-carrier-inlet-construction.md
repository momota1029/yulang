# Returning identity carrier: first complete-inlet constructor cut

Date: 2026-10-06
Baseline: `9c410df85cefdfbb7bfd9c48ddc5052bdb3319d0`
Branch: `research/simple-sub-intrusion`
Status: frozen, independently compiler-referee-reviewed research-only derivation; no findings within the stated constructor scope
Claim class: bounded constructor derivation and exact first missing rule
Authority / implementation permission: none
Exclusive lease: this note only

## Objective and result

For the source candidate

```text
my id z = z
my caller x = id x
caller Unit
```

attempt to establish that the original complete identity Function inlet
admits the particular source carrier `t_R = Delay(result(Unit))`, with its
original descriptor, provider, current world, owner, scopes and one original
`xi=(nu,K,D)`. Unit is the ordinary Unit literal in this proof notation.
The method is backward constructor typing from the complete inlet, followed
by the literal/Result/Reify introduction premises; no control-prefix replay
or executable toy model is used.

The inspected constructors supply a source computation and inert carrier
at the ordinary Unit interface. They do not supply its admission at the
original complete identity inlet. The first missing rule is the
**returning-carrier instance of that complete inlet's independent constructor
typing/admission clause**. This note stops there. It constructs no admitted
complete initial context, satisfying original row, counterexample to source
semantics, or empty-domain theorem.

## Authority, dependencies and hypotheses

The approved
[inlet-domain answer q1/d1](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md),
decisions 1–5, quantifies over all independently typed compatible caller
contexts at the fixed original `(nu,K,D)` and interface. Different programs,
unreached uses, composition and future reuse remain included. Other values,
paths, contracts, origins, continuations, authority and correlations must be
independently valid. Admission is independent of Q. Option 2 remains in force;
production observations do not all require a source-constructor witness.
Approval selects the domain's quantification scope and explicitly excludes
complete descriptor interpretation and completed proofs.

Exact reference sections used:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§2–5: original shared contract, static profile, paths, scopes, one joint
  assignment, Q independence, and explicitly open constructing judgments.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.2,3,6–9,10: active independent descriptor/admission clauses, constructor
  inventory, local typing hypotheses, Option 2, conditional allocation class
  and open coverage. These remain conditional research clauses.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§6,9: ordinary Value parameter generation, source result synthesis and
  the separate carrier-dependent complete invocation. Section 3's structural
  translation is read only to identify the exact Delay descriptor.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §§4,6: executing observations before dispatch, indexed typed transport,
  provider lineage, receipts, exact owner/receiver activity and no authority
  creation. These conditional rules preserve supplied contracts.
- [Prior admission construction](2026-10-06-independent-initial-admission-construction.md)
  §3: the distinct returning ordinary caller and its complete inlet cut.
- [Profile/admission construction](2026-10-06-source-profile-admission-construction.md)
  §§2–5: source constructor schema versus complete original-row satisfaction.
- [Initial-context construction](2026-10-06-initial-context-source-construction.md)
  §§4.2,4.4,5: open Lambda, complete whole-argument compatibility and
  PCInit-source's required satisfaction of independent local relations.

Freeze the following parameters together, rather than selecting their values:

```text
sigma_O  original binder tree and legal original source scopes
xi_O     one original (nu_O,K_O,D_O), with all incidence identities retained
v_id     original identity provider, actual Pure introduction / Value entry
F_id     its original COMPLETE advertised Function descriptor/root
T_id     CarrierContract(F_id), with its original independent interpretation
V_id     complete decorated executing view and original profile inventory
C_0      current world, environment and active caller owner at the challenge
e_R      one original carrier-view packet and source-root witness
```

These are retained dependencies, not established inhabitants of a satisfying
row. In particular, `F_id` is not defined by `Fun(Value(Unit),Comp(empty,Unit))`
and `T_id` is not selected to contain only `t_R`. Generalization/instantiation,
if required to expose the original id at this use, must supply its whole legal
copy at the original scopes; this note does not discharge that dependency.

The local derivation below is conditional on the ordinary Unit literal rule,
legal `xi_O` and its unchanged source constraints, and the independent typing
of `C_0` and its surrounding open environment. An empty import/handler list
does not prove those world conditions. The complete `F_id/T_id` interpretation
and constructor lemma are unsupplied dependencies, rather than hypotheses
silently claimed to follow from ordinary literal typing.

## Proof tree up to the first missing rule

Use `SourceTyped` for ordinary derivation-indexed source typing. Write
`Inlet_F_id(t,C_0;xi_O,e)` solely as notation for the concrete carrier instance
of the already required independent complete descriptor/admission judgment.
This notation neither defines its semantics nor adds a new predicate rule.

```text
ordinary Unit literal rule at sigma_O, under retained xi_O and C_0
---------------------------------------------------------------- Literal
Unit : Value(Unit)
---------------------------------------------------------------- Result
c_R = result(Unit) : Comp(empty,Unit)
---------------------------------------------------------------- Reify / inert Delay translation
t_R = Delay(c_R,original lexical references and packet e_R)
     : Value(computation-data(Comp(empty,Unit)))

above source derivation; original F_id/T_id interpretation;
all original carrier/view/provider/world/scope side conditions
????????????????????????????????????????????????????????????????? MISSING
Inlet_F_id(t_R,C_0;xi_O,e_R)
```

The Literal/Result/Reify steps are the inspected typed-core §6 synthesis
rows and source-contract §3.2 inventory; the Delay descriptor is typed-core
§3's translation. Constructing it executes no argument prefix. The displayed
carrier type is ordinary computation-data typing, rather than a theorem about
`T_id`. Source-contract §2.2 explicitly separates generated constructor image
membership from `DescMem` and requires a constructor typing lemma.

Identity body synthesis supplies this separate tree:

```text
ordinary z parameter: Value(A_z); body binding z : Value(A_z)
name z : Value(A_z); Normalize = result(name z)
---------------------------------------------------------------- Lambda body/result skeleton
Fun(Value(A_z),Comp(empty,A_z))
```

At the proposed Unit specialization, that body result is `Comp(empty,Unit)`.
The specialization is subject to the original whole component constraints;
it is not a proved satisfying valuation. Typed core §9 states that Value
entry identifies the payload after entry demand and does not describe the
complete incoming carrier. The body/result tree therefore supplies no
missing inlet inference.

The required missing instance must validate every relevant original factor:

| Factor | Required evidence at the same original tuple |
| --- | --- |
| Carrier | Exact `c_R`/Delay code root and source tag, with its original packet; no interface-only or endpoint-only replacement |
| Descriptor | Admission according to the actual independently interpreted `T_id` of `F_id`, including retained active incidence predicates |
| Provider | Same original `v_id` and dependent captured/environment roots; complete lambda realization when required, independently of hypothetical target membership |
| Entry/receipt | Original received-carrier position, actual Value entry, designated one-layer Force and typed result rebind to z |
| View/profile | Original complete executing position and all independently applicable original profile positions; their indexed source witnesses |
| World/owner | Independent validity of `C_0`, surrounding environment, actual current owner and exact receiver activity; no revival or invented activation |
| Correlation | Original binder scopes, one `xi_O`, unchanged predicate identities in `K_O`, dependent links in `D_O`, and provider/runtime lineage |
| Continuation | Original designated consumer, invocation return and surrounding suffix, with their independently typed current-state dependencies |

This lists the obligations the missing constructor instance must justify,
not claims that they are all solved or that each needs a newly selected rule.
Existing structural transport gives corresponding indexed preservation only
after typed inputs and applicability/ownership evidence are supplied.

Initial-context §4.4 names the stronger emitted proposition

```text
WholeArgCompatible(Comp(empty,Unit),CarrierContract(F_id);xi_O,e_a).
```

It is whole-interface checking under the independent descriptor kernel,
rather than a single returning observation. The requested concrete inlet
membership is necessary for the desired carrier challenge; proving that
one instance would not prove this stronger whole-interface proposition.
No singleton interpretation of `Comp(empty,Unit)` is assumed. PCInit-source
can consume satisfied local relations, but supplies neither their truth nor
an independent concrete filling certificate. Its hypothetical hole interface
cannot be the last rule in this proof tree.

## Exact carrier identity and downstream obligations

In the displayed literal program, `caller Unit` supplies the literal carrier
`Delay(result(Unit))` to caller. The later `id x` supplies
`Delay(result(name x))` to id, retaining the original rebound x view and
lexical reference. A typed lookup may return Unit; equal returned values do
not identify the two carrier/code roots or their packets.

The requested literal carrier can be considered as a separately supplied
whole-argument challenge at the fixed original identity inlet, using the
approved independent caller-context quantification. This possibility does
not certify its compatibility or replace the program's `id x` carrier.
This derivation proves admission for neither carrier. A Name/lookup transport
lemma could relate their returned Unit views only under its own premises;
it cannot discharge the missing complete inlet rule.

Conditional on admission and the complete typed constructor laws, identity
entry forces this carrier and the Return/Bind unit law reaches the rebound
Unit body result. That operational reduction is downstream of the missing
rule. The complete invocation still includes receipt, actual entry, complete
view, body, designated consumer, invocation return and surrounding suffix;
it is not equated with the empty body row. No trace is executed here.

## Does an approved clause entail the missing instance?

No inspected approved clause supplies it. Q1/d1 says **independently typed
and compatible** contexts belong to the full domain; the missing inlet proof
is part of that antecedent. Its decision 5 excludes complete descriptor
interpretation and proof closure. Inferred call views §§2,5 similarly retain
independent source construction as an open gate.

Source-contract §3.2 prescribes emitted constructor clauses; §3.5 explicitly
assumes the local descriptor typing lemmas before proving C-realization.
Its §§6–8 allocate guarantees relative to supplied independent noncoverage,
value, entry, provider and scope premises. Allocation of no outward request
does not prove inlet validity. Section 10 leaves general source/value/capture
coverage open. Option 2 §3.7 concerns complete constrained membership with
hard guards and separate admission certificates; its identity arm requires
source-base typing already to prove the descriptor envelope. None converts
the above source carrier derivation into the missing independent inlet fact.

This is a bounded source-premise obstruction, not a proof of logical
impossibility across all repository sources. No alternative language meaning
is proposed. The prior trace and this constructor attempt reach the same
complete inlet premise; another returning trace or checker using assumed
inlet rules would leave it untouched.

## Independence, checks, resources and omitted scope

Reference evidence is the named source sections and ordinary constructors,
independent of Oracle behavior and pending Q. The construction shares their
declared descriptor, world, profile and typing assumptions; no independent
implementation oracle is used. A checker implementing an assumed final inlet
rule would prove rule-relative consistency only. No executable experiment,
mutation test, random seed, numeric range or finite enumeration was run.

Logical shortcut audits: replacing `T_id` by this singleton changes the
challenge domain; identifying the empty body row with complete invocation
drops entry/carrier dependencies; deriving admission from a hypothetical
hole typing or Q assumes the missing premise; replacing `id x`'s carrier by
literal code from its equal Unit result loses its original root/view; splitting
`xi_O` across the factor table loses original correlations. These are stated
failure conditions, not run mutation results or source counterexamples.

Checks run: `git rev-parse HEAD`, `git branch --show-current`, narrow status;
bounded `sed`/`rg` reads of named governing sections and dependencies;
`git diff` against the pinned baseline for those exact dependencies;
SHA-256 of pinned `git show BASE:path` bytes compared with current files;
note-local whitespace and relative-link inspection. Initially oversized
combined output was truncated; governing slices used in the derivation were
subsequently reread with bounded captures. No exhaustive repository search
for an unnamed alternative kernel rule is claimed.

Resources: at most four concurrent lightweight read processes per wave;
no builds/tests, Cargo, solver, Oracle execution, child agents, Git mutation
or background processes. CPU/RAM peaks and precise wall time were not
instrumented. Output is this one leased note; no compute budget expansion.
Verification is producer inspection, with independent review pending.

Omitted: complete original row existence; generalized id scheme construction;
complete provider descriptor realization; independently typed prefix/world
existence; stronger whole-interface compatibility; other challenge contexts;
handlers, requests, resumption and production-only providers; production
inclusions, principality and current compiler acceptance. No failure or closure
of these gates follows from this cut.

Recommended next action: have the primary locate or assign the independent
complete Lambda/inlet constructor clause and instantiate its returning-carrier
case at this exact original `F_id,T_id,xi_O,C_0`. Supply the complete factor
evidence before another trace/model. If the clause is not yet specified, retain
that exact semantic-kernel dependency as open rather than select its meaning.

## Independent review

A compiler referee found no blocking, major or minor issue in the constructor
derivation, exact carrier-root distinction, first missing independent inlet
premise, or preservation of the original tuple/scope/profile/provider/world
obligations. Unnamed repository alternatives, implementation and runtime
behavior were not reviewed. No source rejection, complete-row existence or
admission result follows.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-return-carrier-inlet-construction.md`.
- Baseline SHA: `9c410df85cefdfbb7bfd9c48ddc5052bdb3319d0`.
- Dependency changes: none observed; pinned/current SHA-256 match below.
- Review status: compiler-referee PASS within the recorded bounded scope; no
  theorem-gate completion or implementation authority. Writes stop after the
  review metadata update.
- Checks already run: scoped source/rule inspection, exact dependency diff
  and SHA-256 comparison, proof/quantifier/carrier-root audit, note-local
  whitespace and link checks; no builds/tests/probes.
- Proposed commit: `research: isolate returning-carrier complete inlet rule`.
- Shared-record deltas left to primary/curator: link the note if accepted;
  retain independent complete-inlet constructor typing as the first open
  premise, distinguish actual id-x carrier from literal carrier challenge,
  record no original-row witness and no P/A closure. No task/index/authority
  or question-board file was edited.

| Frozen dependency | SHA-256 at baseline and current read |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-independent-initial-admission-construction.md` | `dec2d881c12631477b41a929641d898e0bada936cf7c0ee604cf9e618e1d145a` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
