# Original entry interface and native endpoints: first phase obstruction

Date: 2026-10-15
Job: H1-L constructive leaf; static construction/source bridge
Baseline: `8e7f249cf94c06fb15c3e8da94d41f57c3f8ed65`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research-only bounded derivation and obstruction
Exclusive output: this file only; frozen on handoff
Parent: H1/H2/U OPEN; H3/P disabled
Semantic adoption, production representation and F5 authority: none

## 1. Frozen statement, indices and exclusions

The original parent ranges over every originally admitted shallow Catch at
one original scoped assignment `sigma`, with the original binder tree `B`,
source `X`, `xi=(nu,K,D)` and dependent contexts. It retains every actual
provider and its dependent futures, complete callee/receiver/whole-Call
alternatives, raw resumptions at their actual current configurations, and
distinct consumed, protected, unmatched, outside-arm and resumed residual
contributions. This note changes none of those quantifiers or binders.

The local required conclusion is construction of the original complete
whole-carrier entry interface `I` at its original ParameterOrigin, together
with its lawful interpretation through the actual native parameter Value
row and the applicable Apply argument/value-effect endpoints. Construction
must precede an individual challenge. For every original legal assignment,
every retained actual provider decomposition, and every independently
admitted challenge and development, the same constructed interpretation
must retain the actual provider/event/carrier and all shared evidence. A
schema's construction is distinct from finding an inhabitant, satisfying an
inference constraint, or executing an invocation.

Only the native structural prefix below assumes successful authentic
LocalSource formation/resolution, candidate collection, session initialization
and successful fallible constructor execution. Apply and Lambda effect formulas
are for the candidate graph-effects route. These path hypotheses do not
restrict the parent's admitted source domain or prove that all its inputs
reach this candidate route. Where an original typed predecessor context is
needed, retain it as the parent's input; a HIR scope address does not construct
that semantic context.

No hypothesis supplies `I`, independently chooses a provider, solves a formal,
requires an annotation, turns all Values into Functions, or identifies a
provider-specific contract with the generic formal interface. No compiler
code, test, semantic definition or production representation is proposed.
The result is a bounded source derivation with a first unsupported semantic
rule application, not an established whole-interface theorem, impossibility
theorem, executable probe, counterexample or closure of H1/H2/U.

## 2. Governing sources and three separate interfaces

The governing sections are:

- contextual Function definition, `notes/design/2026-10-08-contextual-function-membership-definition.md`
  §§2–4, and `notes/theory/2026-10-08-call-semantic-input-realization.md`
  §§2–4: independently interpreted admission/observation interfaces,
  same-provider realization, current-event restriction and immutable bindings;
- source-interface definition, `notes/design/2026-10-08-call-source-interface-definition.md`
  §§2–4, and `notes/theory/2026-10-08-call-source-interface-construction.md`
  §§2–5: declared interfaces, IF-Insert/IF-Use and actual producer phases;
- original Call formation, `notes/design/2026-10-07-original-call-formation-definition.md`
  §§2–4, and `notes/theory/2026-10-07-call-input-construction-proof.md`
  §§2–4: original indices, Entry-Value premises, ordered suffixes and
  syntactic whole-substitution;
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5:
  ordinary symbolic generation/accumulation and no solve-at-generation rule;
- `notes/design/2026-10-08-native-recursive-interface-definition.md` §§1–4
  and the candidate `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md`
  §2: exact two-closure scope, independent `I_x,I_y`, and fixed-original
  parameter/guard correspondence requirements;
- reviewed H1-K, `notes/theory/2026-10-15-original-value-descriptor-kernel-audit.md`,
  as the starting obstruction, with H1-I/H1-J as prior routes for the economy
  audit. Their reviews do not review this note.

`notes/design/INDEX.md` locates these scopes. Source contracts
`notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§3.3,3.7
locates the independent history and hard-envelope inputs cited by the
selected Function definition. Its conditional/Draft primitive clauses are
not adopted here.

For a closure `L` with formal `f`, distinguish:

1. L's **incoming** whole carrier, its Value-entry Force and its returned
   value bound to f. The native parameter row represents the Value endpoint
   of that binding; it is not itself the incoming carrier.
2. The Value descriptor of f, which may retain noncallable and callable
   alternatives. On a genuine callable alternative `Act(v,U,r)`, U has its
   own complete entry/observation contract. L's Value parameter role does
   not determine U's role or entry.
3. At a later source Apply `f a`, the whole carrier supplied to U is the
   Call's reified argument. Its native argument Value and evaluation Effect
   endpoints belong to that Apply. They are neither L's original incoming
   carrier nor the row representing f itself.

This separation is necessary even for a direct formal Name. The `I_i` of
the two-closure constructor is the incoming interface of the corresponding
registered closure/formal. It is not a rule assigning that same interface to
every callable value later bound to an arbitrary formal.

## 3. Actual native construction and consumer derivation

All locators below refer to the pinned, unchanged source files. These are
constructor facts, not interpretations of complete carrier membership.

**Source formal and shared row.** `crates/yu-hir/src/module/local_source.rs:229`
stores parameter identity, source origin, scope and optional annotation;
`:386` and `:1014` construct top-level/local parameters at their original
scope chain. `crates/yu-solver/src/candidate_source.rs:273` allocates the
parameter recipe j and one `FormalRegistrationInput`. At `:298` every Name
resolved to this parameter chooses `CandidateEndpoint::Parameter(j)`;
`:327` separately retains its own Name occurrence and registration edge.

`crates/yu-solver/src/lib.rs:10107` appends ordinary parameter bounds/levels
and metadata after the Value components. Source initialization at
`candidate_source.rs:759` validates recipe identity and retains once

```text
q_f = parameter_live_base + j
native_root_f = live_value_term(Positive,q_f).
```

`shadow_apply.rs:1411` computes the same row for either requested polarity.
Thus positive and negative native occurrences have one actual row identity.
The initial empty bound store asserts no semantic emptiness or universal
carrier contract. `candidate_source.rs:579` gives parameter Name evaluation
its own pure Effect constraints; it does not force the incoming carrier again.

**Lambda's native entry-effect prefix.** `lib.rs::admit_lambda_fact` at
`:11254` uses the parameter's negative Value endpoint (or an existing
formal-domain endpoint on the annotation route). On the candidate graph
route it allocates two fresh Effect rows at the parameter level, entry and
returned, and emits with the Lambda's actual provenance:

```text
entry_positive <= returned_negative       [slot 3]
body_effect_positive <= returned_negative [slot 4]
Function+(q_f_negative, entry_negative,
          returned_positive, body_result_positive) <= lambda_root [slot 2].
```

The body result can itself be a parameter endpoint. The first edge is
retained at its owner through `retain_inferred_entry`; raw formal Function
child identity can also be retained as `FormalConstruction` at `:11386`.
These facts support entry-effect accumulation, including an unused formal.
They do not supply an initial-world, typed-path, receipt or carrier-admission
meaning. Allocating these rows after traversing the body also supplies no
independent complete entry-interface declaration at ParameterOrigin.

**Apply's native argument pair.** `candidate_source.rs:604` retains actual
callee/argument children, their Value/Effect endpoints, Call result, checking
occurrence and cause. `shadow_apply.rs::admit_candidate_fact` at `:1427`
checks this recipe/source join. At `:1455` it constructs

```text
callee_positive <=
  Function-(argument_positive, argument_eval_effect_positive,
            invocation_effect_negative, result_negative).
callee_eval_effect_positive <= application_effect_negative
invocation_effect_positive  <= application_effect_negative.
```

The invocation Effect row is fresh at the application Effect's level.
`NativeInterface` retains these exact handles before admission. The demand
is generated without solving the callee or choosing U. If the callee is the
direct resolved Name f, its positive endpoint is the shared q_f endpoint;
wrapper routes retain their actual separate source/endpoint path.

`term.rs:1130` and `:1147` check kind/polarity of the four Function children.
The structured pair consumer at `lib.rs:12551` constructs the four directed
child obligations: upper Argument/ArgumentEffect to lower inputs, and lower
ResultEffect/Result to upper outputs. A live row versus Function demand can
instead accumulate/extrude bounds; generation is not a proof that a positive
Function pair has dispatched. The child equations express constraint
directions, not actual entry/response/raw-resumption actions.

**Source observation consumer.** `candidate_call.rs::observe` at `:342`
checks the actual source Apply, source-owned scopes, demand children, kinds
and polarities, and at `:435` the formal/Name/Lambda route and stored positive
root. It exposes these native fields; it does not consume a complete I.
`PendingCallConstruction::suppliers` at `:280` requests the missing complete
interface and other suppliers. This is an observer, not an implemented
original IF-Use certificate. The mathematical IF-Use rule in source-interface
construction §3.2 consumes the already declared complete interface and its
original legal substitution. These two consumers must not be identified.

No storage, provenance check or child enqueue above proves activation,
complete replay, transport through extrusion/intrusion, or generalization.

## 4. Direct entry construction: the first unsupported application

Apply the actual source constructor from Call-input proof §3.2:

```text
Capture(E,L,E_cap;edges), ParameterOrigin(L,f,Value(A_f),r_f),
original received-carrier port r_in and designated entry view,
original receipt/rebind ports of L
----------------------------------------------------------- Entry-Value
Receive(r_in); Receipt_L; Force_entry(r_in); Rebind(r_in,r_f,A_f).
```

This rule retains the ports and sequencing from its premises. Its semicolons
do not perform the actions. In particular, the premise **designated entry
view** is not a conclusion computed from `Value(A_f)`. The native row q_f
authenticates the result Value endpoint only. The fresh Lambda entry Effect
row and an Apply's argument/value-effect pair add scalar endpoints, without
the original whole-carrier domain or the interpretation of the entry phases.

The selected contextual constructor then forms
`ContextualFunction(Pure,ValueEntry(I),receipt;Force(I);typed-rebind;...)`
from an **independently interpreted** I. Candidate simultaneous introduction
§2 starts explicitly with such `I_x,I_y`. Its admission proof inverts an
already registered closure to obtain `CarrierContract(U_i)=I_i`, then
rewrites the **same** challenge certificate by that equality. No such
equality or challenge certificate is produced by the native row constructor.
For arbitrary callable alternatives of a formal, inversion of one source
closure cannot supply their other original contracts.

The first unsupported application is already the **initial/pre-receipt
interpretation of that designated view**, before receipt, Force, Return or a
pending request. To form the required independent interface one needs its
original domain of compatible initial challenges and observation family at
the original predecessor context. At an arbitrary member of that domain,
the initial observation keeps the same carrier, actual provider, current
configuration/witness, typed paths, scopes, incidences and hard guards,
without claiming receipt has occurred. The types and current-world/phase
action of these fields are missing at the source/native seam.

Concretely, the unsupported step would have to take the actual
ParameterOrigin, predecessor indices and native endpoints to an original
entry-view declaration whose **initial** case has all those dependent
fields and whose native interpretation relates those same endpoints.
There is no independently supplied instance of that declaration/application
in the inspected owners. This is missing schema/interpretation and its
action, not a requirement to prove all guards true or exhibit all possible
challenge inhabitants during inference. Merely quantifying over a named
`D_I` or writing an initial-observation predicate assumes the missing input.

The precise semantic owner is the original whole-carrier/designated-entry-view
interpretation at ParameterOrigin. Source formal elaboration and native
Lambda/Apply construction are its correspondence owners. Contextual Function
realization is a consumer relative to independent `D_F,P_F`; IF-Insert and
IF-Use retain independently typed declarations. Neither is the missing
initial-entry interpretation producer. The first gap is therefore not an
obligation for the propagation scheduler to solve a constraint sooner.

This stop is supported positively by the rule premises and the selected
definition's explicit independent-input boundary. It is not a repository-wide
absence claim or a proof that no dependent interpretation can exist.

## 5. Remaining phase obligations and the joint action

The construction stops in §4. The following specifies coverage required of
the missing original declaration, not further proved constructors or a new
phase semantics:

| Phase/field | Required original meaning preserved at its owner |
| --- | --- |
| Initial/pre-receipt | Independent compatible challenge domain; same current configuration and typed paths; phase guards without an established receipt |
| Receipt and Force | Actual invocation establishes its own receipt; designated one-layer Force uses that same whole carrier at the live event |
| Pending argument | Same operation/request witness, typed response family, raw handle/current resumed configuration and ordered remaining suffix; no f binding before its actual Return |
| Completed entry | Actual returned Value/root/provider and typed rebind at the post-Force world, related to q_f, including latent/noncallable results |
| Later callable use | Same retained `Act(v,U,r)` and complete independent admission/observation contract; no role/entry inference from L's parameter tag |
| Full Call/result/future | Separate callee/receiver/whole-Call slots, every original arm, and the actual output-dependent future/provider/license fields |

Realization §3.1 quantifies over **every** retained genuine `Act(v,U,r)` and
every complete, pending, administrative and zero-step observation of that
U at the same challenge. Its §4.1 restricts binding certificates only along
independently compatible event extensions. An event's configuration is live;
fixing sigma is not freezing the maker's state or preserving an expired
grant. These established conditional consumers must be preserved when the
missing declaration is supplied. Noncallable alternatives retain their own
membership/root/incidence meanings; they are not assigned artificial U's.

The necessary one-sigma discipline is:

```text
construct original declarations at their original binder positions;
evaluate all shared fields by the same original sigma restricted there;
for an original legal whole substitution m, transport that entire
dependent tuple, its K,D, imports, incidences and evidence together.
```

Call-input proof §4 proves this action on the static constructor syntax.
Source-interface construction §§3.1–3.3 assumes the original lawful action
on primitive/interface meanings and retains it. Thus semantic compatibility
of the entry domain, initial guard and observation family under m remains
part of §4's missing owner input. In particular identity/composition of a
syntax substitution does not establish a guard's semantic action. No new
map is declared lawful here.

For a pending request, the response and raw-handle fields are dependent on
that very request and current resumption event. For a returned provider p,
its future field is the original `Future(p,current_C,...)`, including its
own admission/license. A W/Z alternative introducing p' retains that arm's
own dependent fields at p'. Neither a marginal witness per field/use nor
the structural provider's contract can be substituted. Witnesses introduced
at later original dependent scopes remain there; one sigma is not an
existential witness chosen above all challenges.

The approved native recursive interface definition does not bypass the
stop. Its §§1–2 select the entire typed presentation of the exact immutable
pair, with full pullbacks only for genuinely missing native parameters in
that interpretation. Fixed-original guards/actions require actual typed
identifications and laws; guard truth is separately required at an actual
tuple. The implementation's q_f and four Function handles have not been
identified with that entire copied presentation. Extending its selected
two-closure definitions to arbitrary formal registration would exceed its
scope.

## 6. Economy audit and one next action

H1-I's forward registration and H1-J's generic-descriptor construction left
the original dependent interpretation missing. H1-K identified the direct
constructor's independent I premise. This packet inspects the actual native
entry Effect producer and applies the original Entry-Value/ContextualFunction
rules directly; it stops at their designated-view initial interpretation.
It does not start another generic-interface or fixed-point variant after
that stop.

Under `rules/compiler-engineering.md`, agreement of the original entry
contract and native constructors remains A/B for the existing hygiene and
natural-inference parent. A complete global descriptor universe or equality
with every foreign model is not made an additional prerequisite. The
already retained source identities, shared row and scalar provenance are
D facts; copying them again cannot supply a carrier/phase interpretation
unknown to those constructors. If the original declaration owner already
has this interpretation, retaining its canonical declaration/map can remove
reconstruction. This audit neither adopts such a representation nor closes
the parent gate.

**Next action:** primary should route the exact designated-entry-view
initial-case declaration/action at ParameterOrigin to its original semantic
owner: supply its independent current-world/phase/typed-path domain and its
actual native-endpoint interpretation, or identify the first genuine
unselected semantic choice there. The decisive evidence must change that
premise. Another pending graph shell, per-use provider contract, scalar
effect equation or syntax-substitution proof leaves it untouched. This
bounded obstruction alone establishes no need for a user decision.

## 7. Evidence, limits and runtime settings

Reads used `cat`, `sed`, `rg`, `wc`; hashes used `sha256sum`. Startup read-only
Git inspection observed the full pinned HEAD and a clean working tree.
Large aggregate captures truncated; decisive sections and source bodies
were reread in narrow ranges. Handoff validation checked all 29 recorded
SHA-256 rows: all match the inspected files. Of 28 repository dependencies,
27 match the baseline bytes. H1-K alone has the review-status wording delta
recorded below; its mathematical premises and all six native source files
are unchanged. Twelve fence markers balance and no trailing whitespace was
found. Read-only final status shows this note and the separately leased
falsifier note; this leaf wrote only this note. These are static evidence,
not tests or independent review.

Zero tests, builds, executable probes, benchmarks, measurement samples,
delegations or Git mutations. One leaf; serial lightweight read/write
commands only; packet wall-time cap 25 minutes. Exact elapsed time, aggregate
CPU and peak RSS were not measured and remain unknown. The primary retains
verification/integration ownership. No shared record or compiler file is
written by this leaf.

Requested route: normal Sol proof leaf, `gpt-6.1-sol/high`. The callable
schema offers `prover`; `.codex/config.toml` registers it and Sol/high
subagent defaults, while `.codex/agents/prover.toml` omits model/effort pins.
Observed effective runtime model/effort metadata: unavailable/unknown. No
override, hot reload or Astra execution is claimed.

Unverified: all-source admission/reachability; actual whole I/native semantic
interpretation; pending/receipt/Observe/expiry execution; complete Call/C0;
lawful semantic guard action; constraint activation and complete replay;
levels/extrusion/intrusion/generalization preservation; all residual hygiene;
soundness, required principality and F5. This result supplies no source-qualified
counterexample and has no independent review yet.

### Direct dependency SHA-256 snapshot

No dependency below was changed by this leaf. Repository dependencies were
checked against the pinned commit on handoff; the external skill has no
repository baseline. Task records were read only for context.

Concurrent primary-owned dependency delta: H1-K's §4 wording changed from
requiring fresh review to recording the completed no-findings review. Its
baseline SHA-256 was
`42030d27539345c3927acb504869fc189346e0a6f6fa34afc31cb388c5fa783e`;
its inspected hash is the `3517be78...` row below. The exact delta changes
no constructor, semantic input or theorem premise. Observed HEAD at this
validation was `146ca9d2a8713398c893a9cae026ae0c2fae593d`; the assignment
baseline remains unchanged.

```text
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5  rules/orchestration-budget.md
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
461780f1574b83aacf86921997927e01794169b848835636cf9a2c8f3e9019c1  notes/design/INDEX.md
3517be78abe1b701bf634ce6832206a44e0a39ca1823867665f943424d108d8a  notes/theory/2026-10-15-original-value-descriptor-kernel-audit.md
9b7a7e6a5964ec7da1a4afd2ea44af98792bdc630f76119ce02dab6af543f6e7  notes/theory/2026-10-15-formal-registration-interface-construction.md
43f5752bf802f14ca1868806aa60e33236ab67f466251cf488d2a6e330555158  notes/theory/2026-10-15-symbolic-value-interface-basis-construction.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903  notes/design/2026-10-08-native-recursive-interface-definition.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b  crates/yu-solver/src/candidate_source.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac  crates/yu-solver/src/shadow_apply.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60  crates/yu-solver/src/term.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199  crates/yu-solver/src/candidate_call.rs
db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810  /home/momota1029/.codex/skills/yulang-proofs/SKILL.md
```

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-15-entry-interface-native-bridge-construction.md`.
- Baseline SHA: `8e7f249cf94c06fb15c3e8da94d41f57c3f8ed65`.
- Changed dependency hashes: none authored; concurrent H1-K review wording
  changed `42030d27539345c3927acb504869fc189346e0a6f6fa34afc31cb388c5fa783e`
  to `3517be78abe1b701bf634ce6832206a44e0a39ca1823867665f943424d108d8a`;
  remaining 27 repository dependency bytes match the baseline.
- Review status: unreviewed research-only bounded derivation/obstruction;
  no theorem or implementation certification; H1/H2/U OPEN, H3/P disabled.
- Checks already run: narrow constructor/consumer and governing-clause
  inspection; all 29 dependency hashes match; 28 repository dependencies
  compared to baseline, with the sole review-wording delta above; balanced
  fences, no trailing whitespace and narrow final status/diff inspection.
  No tests/builds/probes/measurements.
- Proposed checkpoint message: `research: locate original entry initial-phase interpretation seam`.
- Shared-record delta left for primary/curator: H1-L derives actual native
  row, Lambda entry-effect and Apply prefixes, then stops at the designated
  entry view's independent initial/pre-receipt interpretation/action at
  ParameterOrigin. Keep complete pending/future semantics and source/native
  correspondence open; apply no semantic adoption or parent promotion.
