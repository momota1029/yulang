# Original call registration from the verified lexical source component

Date: 2026-10-06
Baseline: `e2bd3a4d7423b4152b45e79057ad1f1a89979671`
Branch inspected: `research/simple-sub-intrusion`
Status: frozen, unreviewed research-only derivation attempt
Exclusive lease: this file only
Gate/method: O; constructive source-component derivation followed by premise inversion
Implementation/semantic authority: none

## Objective and result

Attempt to derive the original comparison-independent call contract and
receipt from the concrete lexical component of exactly

```text
my apply f = { my step x = f x; step }
```

The newly verified CST/shadow correspondence makes the lexical input concrete:
the local callee occurrence resolves to the outer formal, the argument to the
inner formal, and the returned function retains that outer capture. It does
not introduce a typed contract at the outer formal's inferred endpoint.

**Claim class: bounded derivation prefix and exact premise inversion.** The
ordinary core rules, conditional on their stated fragment and typed premises,
construct fresh endpoints, shared same-binder name references and symbolic
call constraints. No inspected conclusion introduces the complete shared
role-indexed original relation, its profile inventory or typed receipt from
those inputs. This attempt stops at the same O introduction leaf as the prior
registration construction. The additional verified lexical input removes
uncertainty about the selected occurrence; it does not close O or supply a
new semantic counterexample. No further equivalent probe is warranted.

## Authority and explicit hypotheses

Governing authority is inferred Function call views §§1.1–5, the integrated
`function-call-view-formation/q1` answer a2 and receipt, and the exact nested
source addendum §§1–3. These select the source meaning and shared formation
direction while explicitly leaving concrete generating judgments open.

The source addendum establishes sequential binding, function-value return
without invocation, `f`/`x` resolution and retention of that same outer `f`
for later calls. It does not select recursive-group or local-polymorphism
rules. The earlier approved `apply f x = f x` formal/use direction remains
in force: annotation absence causes full protection; the internal Handler
seed is refined by ordinary-value evidence on the shared relationship.
Neither Value parameter entry nor a concrete supplied callable rewrites an
actual callable's role. Full protection does not imply an empty effect row.
There is no `[io]` annotation in this exact candidate.

Hypotheses for the attempted prefix:

- H_lex: the approved exact source and its finite CST/shadow lexical
  correspondence, with occurrence locators and artifact-branded identities.
  This is established bounded structural evidence at the pinned baseline.
- H_core: the ordinary parameter/name/application/lambda/bind fragment of
  typed-computation-core elaboration §6 applies. Its displayed construction
  is conditional research material; it does not grant production authority.
- H_symbolic: fresh endpoints are constraint coordinates in one derivation,
  without independently chosen semantic port witnesses or assumed solving.
- H_typed, if used: the admitted typed-flow, contract and receipt references
  required by core §6 exist. This is a candidate additional premise, **not**
  supplied by H_lex, and is deliberately not assumed for an O conclusion.

The theorem dependency map is a locator/status constraint. Its §§FVIEW/SRC
discussion at lines 130–150 records the open source producer, separately open
attachment A, and conditional prior results. It supplies no generating rule.
The prior constructive registration and falsification notes are retained as
failed routes and necessity evidence. The Q-independent source-rule attempt
separates O from A; its stipulated original receipt is not reused as a fact.
Frozen Oracle was neither read nor used as a premise.

## Concrete source component and artifact correspondence

Use proof names `d_apply,d_f,d_step,d_x` for binding/formal occurrences,
`u_f,u_x,u_step` for the three relevant name uses, `l_apply,l_step` for the
two lambdas, and `c` for the inner ordinary application. Proof names introduce
no compiler object or new language rule. H_lex gives the following incidence:

```text
l_apply(parameter d_f,
  bind d_step = l_step(parameter d_x,
                       call c(callee u_f -> d_f, argument u_x -> d_x)),
       return u_step -> d_step))

capture(l_step,d_f,u_f,position(u_f))
```

This is a single finite *lexical* component assembled from approved source
ownership and resolution. Its three lookup edges do not identify `d_f` with
`d_x`, and its returned-use edge does not invoke `step`. No recursive edge
occurs; selecting a general relevant recursive-component closure is omitted.

| Source fact | Retained artifact correspondence | What it does not establish |
| --- | --- | --- |
| Binding/header occurrence and lexical ownership | `NestedLocator(path,kind,range)` and branded `BinderId`/`PositionId` | Typed ownership, contract scope or a dynamic activation |
| `u_f -> d_f`, `u_x -> d_x`, `u_step -> d_step` | `Form::Use { binder, occurrence }` | A typed Function path, receipt or original joint assignment |
| Inner `f x` | `Form::Apply { source_form, callee, argument }` | Complete Function membership or call-view realization |
| Capture of the outer formal at the local callee | `CaptureUseIncidence(lambda,captured,occurrence,position)` | Original certificate formation O or its later attachment A |
| Sequential local binding and returned function | `Form::Bind` and the two `Form::Lambda` nodes | Generalization, typed capture transport or later receiver realization |

The direct code windows show the CST locator construction, shadow
normalization, source-expression representation and incidence/pending fields.
The reviewed differential record supplies the result of the complete separate
lexical projection and focused test; this lane did not rerun it or read its
entire test body. Both closure markers remain
`PendingTypedCaptureProviderReceiverAndSemanticDischarge`.
`QIndependentSourceCallViewFormation` is an unmet per-call reference to the
shared producer, alongside callable role, membership and realization. It is
not a certificate or an introduction rule.

## Forward relational prefix

Core §6 parameter generation and name synthesis give, under H_core:

```text
P_f = Value(A_f), Gamma(d_f) = Value(A_f)
P_x = Value(A_x), Gamma(d_x) = Value(A_x)
I(u_f) = Value(A_f), n_f = result(name d_f)
I(u_x) = Value(A_x), n_x = result(name d_x)
I(c) = Computation(E_c,A_c)
d_c = reify(call(n_f,n_x))
```

The ordinary argument tag is determined before solving `A_x`; substituting a
latent value endpoint does not change that tag. The call constraint identifies
a Function interface at the result of `n_f` and relates the **whole** argument
computation to its parameter, retaining typed-path/contract obligations.
Generating these constraints certifies neither a solution nor their typed
boundary premises. In particular it neither identifies `A_f` with a complete
registered view nor computes effects as a portwise row union.

Lambda synthesis can describe the symbolic local interface as
`Value(Fun(Value(A_x),Result(I(c))))`. Ordinary binding then binds `d_step`
to the RHS result endpoint and the final name copies that endpoint. Its
`E_bind` remains subject to the existing complete binding relation; no empty
construction effect is inferred here. The structural correspondence from the
addendum is thereby the target of a conditional core derivation, with the
administrative Normalize/reify conventions retained. It is not a typed
decoration theorem generated from the raw CST.

This prefix is relational only in the weak, explicit sense that the same
symbol `A_f` occurs at the formal and its resolved callee use. It supplies
endpoint sharing and generated obligations. It is not the stronger original
source relation over completed views and joint `xi=(nu,K,D)`.

## Premise inversion: the minimal missing introduction

To conclude O at `u_f`, the derivation must introduce, at `A_f`, one shared
inferred formal/use relation tied to this concrete lexical component and
annotation absence. Its conclusion must expose the original contract,
`beta`/`Slots(beta)`, role/entry relationships, typed incidences, and constraints
on the **whole** original `xi`. Those are the objects required by call-view
§§2,5; naming them in a conclusion is not a proof rule.

The inversion of the inspected rules is decisive:

| Candidate last rule | Actual premise/conclusion | Unsupplied input for O |
| --- | --- | --- |
| Name synthesis | Copies `Gamma(d_f)` to `u_f` | The complete registered original relation must already be in the environment |
| Application synthesis | Generates Function/whole-argument constraints with existing typed obligations | A source rule connecting those constraints to the original contract/profile and typed boundary evidence |
| Parameter entry | Fixes Value entry and a finite receipt skeleton; receipt paths retain admitted typed-flow premises | The matching original contract and typed receipt-path correspondence |
| Lambda/local bind | Composes interfaces and rebinds the RHS result endpoint | The missing original relation is not introduced by returning its consumer's closure |
| Pending shadow premise | Names the unresolved shared producer on `c` | No generating conclusion at all |

Thus the first missing input remains an **introduction rule from the resolved
formal/use component to its shared original typed relation**. The lexical
component now has a verified concrete witness, so unresolved lexical lookup
cannot explain that missing rule in this candidate. Conversely, a fresh
Function endpoint, an alias of `d_f` called `beta`, or an empty profile list
would not construct the required contract/profile.

There is a necessary static/event distinction within the bundled O obligation.
The source producer must first give a comparison-independent original
contract/profile and typed receipt *schema*. At a particular outer entry,
the original actual receipt must then relate that schema to the provider
received at that entry using admitted typed paths. Core §6 says Value entry
establishes an actual receipt, but expressly retains those typed premises.
The CST alone names neither an enclosing activation nor a concrete provider.
Postulating `Original(d_f,r_A,g,C_f,R_f;xi)` would skip both the missing static
introduction and its required typed event instantiation. This distinction
splits proof inputs; it selects no new runtime policy or language meaning.

Even granting such an original certificate would only move the proof to A:
attachment and captured lookup preserving that whole certificate. It would
not establish A or a later active receiver. Preserving static source identity
does not preserve an expired activation as active. Generalization/use-time
freshening must transport the whole original relationship; fresh variables
for distinct uses are permitted with a certified original correspondence.

No conditional theorem of the form “H_lex implies O” has been proved. The
valid conditional statement is only: **H_lex and H_core support the symbolic
prefix; a completed O derivation additionally needs the missing original
typed relation introduction and its typed receipt instantiation.** This is
a bounded rule-interface characterization, not a global impossibility proof.

## Evidence quality, coverage and stop condition

Oracle independence: the source/shadow differential shares parsing and source
chain association, while its lexical projection and shadow projection have
separate lookup/binding-order implementations. It validates occurrence
structure under the approved exact interpretation. It is not independent
validation of typed transition rules, and this derivation relies on its
reviewed record rather than claiming independent certification of it.
The core derivation and any future checker would share H_core and H_typed;
agreement would not establish that H_typed follows from source.

Coverage is one exact candidate, three name incidences, one inner call, one
captured callee, and the named ordinary core rule interfaces. No numerical
seeds/ranges, random cases, executable mutations or semantic experiments were
used. Prior destructive-shortcut and recursive-self-edge witnesses were read
as necessity results and not repeated. There is no accepted-source
counterexample, public-type discriminator or new satisfiability result.

Failure conditions for a proposed completion: assuming the original
certificate in Gamma; forming `beta` from position alone; inventing the typed
incidence from solved type shape; using Q success to mint a receipt; combining
independently chosen port witnesses; confusing static capture with an actual
receiver; or treating absence of a displayed rule as global source
impossibility. Any newly located in-scope generating rule would require a
fresh bounded derivation from its exact premises.

Stop condition reached: the concrete lexical input leaves the same O premise
untouched. No second toy model or larger enumeration was attempted.
Unverified: general recursive relevance, generalization/instantiation, complete
role/profile inference, seed discharge, annotation contribution mapping,
typed receipt formation, attachment A, later receiver realization, complete
independent admission, production Option 2 extras, principality, adequacy,
production acceptance and implementation. Neither selected source meaning
nor a prior gate is reopened.

Recommended next action: the primary should obtain one narrow proposed
source-component introduction judgment whose output is the original typed
relation and receipt schema at `A_f`, with explicit admitted-path premises
for event instantiation. Review that rule against the approved formation
direction before scheduling another consequence checker or implementation.

## Commands, resources and frozen dependencies

Read commands: policy `cat`; bounded `rg` locators; authority/prior-record
`cat`; one current-task locator window; sequential Python-driven read-only
`git show BASELINE:path` extraction of named record/code ranges; and
SHA-256/worktree-byte comparisons. Nine static read command captures included
three locator captures. Fourteen semantic file/range windows were read,
including a narrow recovery of the truncated prior falsification capture;
the three mandatory policy files were read separately. If the assignment's
14-window ceiling includes mandatory policy files, this accounting is 17,
and therefore exceeds that interpretation by three. No further source reads
were made. The initial broad locator capture and batched prior-record capture
were truncated; no exhaustive repository search is claimed.

All 15 direct frozen inputs below matched their pinned baseline bytes before
the artifact write. HEAD then equaled the assigned baseline. No dependency
was modified by this lane. Later concurrent drift is the primary's
integration-time recheck responsibility. The artifact absence guard passed.
Only the leased note was written; writing stops before review submission.
Zero tests/builds/probes, Git mutations, children or network queries.
Commands were serialized, with one top-level command active at a time and
sequential read-only Git subprocesses. No compute search was run. Shell
captures reported about 0.0–0.1 seconds each; aggregate CPU, peak RSS and
agent wall time were not instrumented and remain unknown.

| Pinned input | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/theory/inference-theorem-dependencies.md` | `620ac10daf177bcb6c4d404035231ceb8c7d591b9f56522fc77223c7825d2edd` |
| `notes/progress/2026-10-06-source-registration-constructive-derivation.md` | `b4d15fd017085f0b58836be544c576d1ce94b1f869482496d1c0507eecd24bd9` |
| `notes/progress/2026-10-06-source-registration-falsification.md` | `1efe0a779c5708a7eedf047c03cdc2764c07d75328bc055cc362d6cc8f58e292` |
| `notes/progress/2026-10-06-q-independent-capture-source-rule-attempt.md` | `52ebde5ee3256dbc6eb88f1c0c5fb07c2980b7d4d4363c5b50fa9b129c6c41c7` |
| `notes/progress/2026-10-06-shadow-nested-source-core-differential.md` | `df8493f4b08c0c582025ba715f483c2b7fc58a87f7eed444a68d75e46aac5840` |
| `crates/yu-hir/src/tests/shadow_source_core.rs` | `b5a8022fd65f55f606b91f7c0a3b533a6cf0f0260633e96ebbb76173bdbb8ead` |
| `crates/yu-hir/src/shadow.rs` | `fa539b61f76c01897d57f03e466a47c24752045489e3804c13278b09ea2e2216` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-original-call-registration-source-producer-attempt.md`.
- Baseline SHA: `e2bd3a4d7423b4152b45e79057ad1f1a89979671`.
- Changed dependency hashes: none observed against that baseline; frozen
  hashes above. Historical producer-note baselines are not substituted for
  current dependencies. Later drift must be rechecked by the primary.
- Claim/review status: frozen unreviewed research-only bounded prefix and
  premise inversion; no independent review, O/A closure or implementation
  authority. The producer does not certify this artifact.
- Checks already run: governing-source and narrow rule-interface inspection,
  pinned/live byte equality and SHA-256 inventory, baseline/branch and lease
  absence checks. No tests/builds or semantic probes.
- Proposed checkpoint commit message: `research: attempt original registration from verified lexical source`.
- Shared-record deltas intentionally left for primary/curator: lexical input
  now has a concrete verified CST/shadow witness, but the O introduction rule
  remains missing before typed receipt instantiation; A and later receiver
  realization stay separate. Do not promote source formation, principality,
  adequacy or production status. No shared record or question bundle changed.
