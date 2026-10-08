# RT.2 apply hole: joint source-front construction order

Date: 2026-10-08
Status: unreviewed conditional constructive attempt; research only
Baseline: `d2a21c4a6246173c906c0be9a1337160ea50409c`
Exclusive lease: this file only
Method: one clause-level construction of the apply front, followed by its captured-step front
Semantic adoption, implementation, full postfixedness and gate closure: none

## 1. Objective and achieved boundary

Attempt the exact apply-hole case of RT.2 for

```yu
my apply f = { my step x = f x; step }
```

The useful construction order is: first derive the native apply Function
front against a joint candidate S, using the selected positive Return clauses
with candidate step fields; then derive the distinguished step's Function
front when its actual captured f is apply, by using that **constructed apply
front**. The candidate contains every actual step allocated by admitted apply
invocations, not only this distinguished step. None of those candidate value
fields is itself asserted to be an output front.

Conditional result: under the explicit RT.1/RT.3 source/background/guard inputs
and the actual native-use identification in §2, the structural source cases
construct the apply front and the distinguished apply-capturing step front,
plus the listed source world/carrier/continuation fronts. The full joint
postfixed proof stops at other allocated steps whose captured f needs the
unavailable relative comparison N_S. This is a source-front order lemma,
not full RT.2, S-postfixedness, OuterNat or final apply membership.

Claim classes: selected constructor inputs reused; conditional local front
derivation; candidate enlarged S; exact remaining comparison/background/action
premises. No independent review of this attempt is claimed.

## 2. Selected inputs and exact hypotheses

Governing inputs:

- [Outer apply introduction](2026-10-08-outer-apply-closure-introduction.md)
  §§2–6: native Strict interfaces; RT.1–RT.3; exact value holes; unchanged
  complete domains and original whole witnesses. Independently reviewed
  conditional theorem, not a supplied RT packet.
- [Captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
  §§2–4: Authoritative Strict, F_step/R_local, selected finite source cases
  and exact local constructor envelope.
- [Captured introduction](2026-10-08-captured-call-closure-introduction.md)
  §§3–6: complete Strict clauses, finite source witnesses, full relative
  background and original source constructor proofs.
- [Call input realization](2026-10-08-call-semantic-input-realization.md)
  §§4–6: immutable binding projection, Name/Return/Delay, independent challenge
  assembly and same-actual-provider elimination. Its final-model VIncl theorem
  is not applied to an arbitrary S certificate.
- [Simultaneous interpretation](2026-10-08-simultaneous-immutable-root-introduction.md)
  §3, as selected by contextual Function membership and captured closure
  definitions: positive Phi on V/W/T/Car, full binding fields and original
  immediate guards.
- [Previous RT.2 attempt](2026-10-08-rt2-relative-transfer-proof-attempt.md)
  §§3–4: N_Z remains missing; enlargement alone does not construct fronts.

The assigned workflow/authority/concurrency rules remain in force. This job
does not select a language meaning or consume pending decisions. The prior
CallInitial owner audit is not a premise: the later selected captured source
constructors provide their original finite source cases in this constructor
interpretation. No correspondence to a separately fixed foreign E is claimed.

Fix the exact native descriptors and original dependent ports:

```text
R_c = ReadInvoke(F_c,D_c,IF_c)
F_step = Strict(I_x,x:A_x,R_c,IF_step)
R_local = selected ordered local-Lambda Return / actual step rebind / Name Return
F_apply^nat = Strict(I_f,f:A_f,R_local,IF_apply)
a = actual original outer apply value at its original root
s0 = actual step allocated after one admitted outer carrier Return of that a.
```

Keep the original B/X/assignment, xi=(nu,K,D), source occurrences, actual
registration/capture/rebind/return incidences, complete challenge domains and
joint scopes. Each use has its actual live C,w; sibling fields must agree.
The actual s0 capture is the same a/root, with no maker activity saved as a
grant. The complete native invocation includes I_f/I_x effects and divergence.

Hypotheses, rather than concealed outputs:

| Input | Required independent content |
| --- | --- |
| H_source | Actual immutable source formation, registrations, capture references, constructor inversion and original raw invocation/entry/Bind/return rules. Every immediate license/profile/path/scope/authority/incidence guard is supplied at its actual event; none asserts final own-member/world validity. |
| RT.1 | All background proof fields for every unchanged independent challenge, response/resume/future demand have their actual full relative V/W/T/Car interpretation at the same tuples. No foreign certificate is merely relabelled; no unsuccessful case is filtered out. |
| RT.3 | Original whole-argument checking, challenge assembly, lawful rebind/restriction/return actions and full primitive/arm contracts apply at these relative tuples. Their hereditary fields map positively along inclusion; non-hereditary guards and domains stay fixed. This is a semantic supplier requirement, not static IF incidence. |
| H_diag | At the distinguished inner use of captured a, the actual checked complete F_c is F_apply^nat at this same whole original tuple, or has a supplied evidence-preserving whole identification of its complete clauses/ports. It is not inferred from printed Function shape, descriptor IDs or projected effects. If this identification is absent, the apply front remains native and the checked-use conversion stays open. |

The construction does not require ordinary final M membership of a, a completed
final world containing a, ordinary final membership of every returned f, or
RT.2 as an input. N_S is explicitly **not** granted for the two local fronts
below. It remains needed at the later uniform postfixed boundary.

## 3. Joint candidate and background readouts

Let H contain only the exact a at F_apply^nat and s0 at F_step, with their
original lawful restrictions. Use the outer theorem's same-operator relative
background

```text
B = nu (Y -> Phi(Y), with only V augmented by H).
```

No world, carrier, observation, continuation, guard or arbitrary returned
provider is a hole. B is an auxiliary mathematical background; RT.1 must
justify the actual proof fields' interpretation in it. It is not an assumed
final model.

Define S by retaining B componentwise and adding the authentic source tuples:

- V: a, every actual step s_i allocated by an admitted apply invocation,
  at the selected F_step port with its actual captured f_i/root and restrictions.
- W: their actual installation/construction, entry, parameter and sequential
  result-binding worlds. Every installed background binding is retained.
  f/x/result bindings appear only after their actual Return/rebind.
- T: their actual complete/pending/administrative/zero-step observations and
  independently admitted finite developments at the selected descriptors,
  including original request/response/raw-continuation and suspended suffix
  fields. These additions are tuples whose fronts still need proof.
- Car: actual inert Name x Delay carriers at original reify origins, their
  designated live demands, and original captured references. Arbitrary external
  entry carriers remain B fields, not substituted by these Name carriers.

Quantification is over actual source allocation/operation witnesses and every
original demand. This may be an infinite family; each raw source observation
still has a finite derivation. No finite allocation/trace bound is introduced.
No allocation-age ordering, fresh-provider injectivity or absence of cycles
is assumed. The proof uses original identities and can keep aliases.

Background fronts are available **by unfolding**, not candidate inclusion:

```text
B.W   -> Phi(B).W   -> Phi(S).W
B.T   -> Phi(B).T   -> Phi(S).T
B.Car -> Phi(B).Car -> Phi(S).Car
non-hole B.V -> Phi(B).V -> Phi(S).V.
```

The last arrows use positivity and B <= S, preserving the entire dependent
clause readout. Each W front includes every binding and joint guard; each
Car front includes inert fields and every Force/response/continuation/future
field. Hole V has no such unfolding; its required fronts are constructed next.
Continuation readouts remain in the original T/pending clauses and carrier
families; no additional semantic sort or assumed continuation safety is added.

## 4. First source front: apply against S

The following constructs each clause of Phi(S).V(F_apply^nat,a), conditional
on §2. It does not use the desired Step or RelativeBlock theorem.

| Clause | Source construction and exact recursive premises |
| --- | --- |
| Actual decomposition/captures | Original outer Lambda inversion supplies Act(a,U_apply,r), actual Pure role, ValueEntry(I_f), stored block code and original capture/registration evidence. Every retained actual decomposition is handled through its same source inversion. Captured fields use their original S.V/S.Car tuples and actual scope; immediate formation guards are H_source inputs. |
| Actual acceptance | For every full independently admitted d, inversion gives CarrierContract(U_apply)=I_f. Rewrite the same d whole-carrier certificate by that constructor equality and pair its independent receipt/path/context guards. This derives ActualAdm before receipt; it changes no domain. |
| Initial/receipt/Force prefixes | Original raw phase/receipt transitions supply their actual guards and world. Strict's prefix clause uses that S.W field and the entire suspended Force/rebind/block/return/future interface. No f, step or result is installed early. |
| Carrier progress | Unfold the same B.Car entry carrier. Each actual Force observation supplies its full T/current-W/response/raw-handle/value fields; the background readouts above map them into Phi(S). The carrier can request or diverge, with every finite prefix and no manufactured Return. |
| Pending/continuation | Original Bind keeps the same request and k at current C. Raw resume develops k(response,C') and only the unfinished suffix: rebind f; inert local step formation; rebind step; final Name Return; invocation Return. Original response/handle/action guards come from RT.1/RT.3 and the actual raw history. Receipt is not replayed. Strict's pending clause uses these exact dependent continuation fields. |
| Actual f Return/rebind | Entry carrier Return supplies the same f_i/root at A_f, its B.V field, current B.W and actual original rebind evidence. PhiW constructs the result-extended S world from **every** old binding, this S.V f_i and the joint registry/authority/incidence guards. No f_i Function front is needed merely to bind its value. |
| Inert local Lambda | The source Lambda witness allocates the actual s_i with its original capture(f_i), code, F_step/IF_step ports and formation guards. The candidate has this S.V(F_step,s_i) field; it is a recursive premise, not Phi(S).V membership. Lambda formation executes neither s_i nor f_i. |
| RHS and final result T fronts | Selected PhiT(PureReturn(F_step)) uses S.V(F_step,s_i), the same S.W and original result/provider/root incidence. PhiW installs that same s_i at its actual sequential binding edge. Final Name selects that exact binding; PureReturn again gives a Phi(S).T front from the same value/world fields. Ordered Bind composes those original dependent fronts and their actual shared middle witness into R_local, including its prefix cases. |
| Invocation return | Strict's actual return map preserves the actual s_i/root/current world and its full F_step future slot. Its original action removes only this invocation's actual occurrence. Hereditary future value obligations use the same S.V(s_i) at every compatible future event; returning s_i performs no future execution. |
| Independent alternatives | Each original W/Z arm uses its own complete RT.3 contract and relative field/action readout, never the unrelated structural U_apply. Changed admission coordinates need that arm's actual domain certificate. If any arm has only a final-M law, this row is open; the arm cannot be dropped. |
| All later demands | Repeat the same clauses at each original independently compatible event using the original whole restriction actions. The front quantifies over all d and finite raw developments, not the invocations already inspected. |

PhiW and the PureReturn/prefix/Bind clauses here are genuine output readouts
whose recursive fields are S premises, as the selected Phi definition allows.
The derivation checks their independent guards and full dependent maps; the
statement “s_i belongs to S” alone would not construct any of these fronts.

For the structural branch this yields

```text
A_front : Phi(S).V(F_apply^nat,a,original root/event).
```

The table constructs the associated source W/T readouts and full outer pending
continuation family. It proves no Phi(S).V front for an arbitrary s_i yet.
An independently fixed A_apply or different checked F_c still needs its actual
complete conversion; native construction does not overwrite that endpoint.

## 5. Second source front: the actual step capturing apply

The distinguished s0 has actual capture f=a by its source construction. Its
capture's S.V(A_f,a) field comes from that actual entry Return/background tuple.
Its **checked** callable front comes from A_front at H_diag, not by eliminating
the capture's candidate membership as Function realization.

Construct Phi(S).V(F_step,s0) clausewise:

1. Actual local Lambda inversion retains the same provider, Pure role,
   ValueEntry(I_x), code and capture(a) root. Registration/capture guards are
   original inputs. For every independent challenge its CarrierContract is
   I_x, so the checked carrier/receipt preconditions construct ActualAdm.
2. Every arbitrary I_x Force/pending/raw-resume/Return case unfolds its B.Car
   fields as in §4. PhiW installs x only after its actual typed Return, with
   all old fields and the actual joint rebind guard. No second latent Force
   is added. Prefix/continuation clauses retain precisely rebind-x, inner Call
   and invocation return.
3. In that world Name f selects the same a/root; Name x selects actual x.
   Their raw Name/Result witnesses are independent selected source cases.
   PhiT Return/prefix uses their S.V/S.W fields at the actual current event.
4. At actual callee Return, inert Delay stores whole q_x and its original
   capture references/license. Its PhiCar inert front uses S.V(x), S.W and
   original guards. At each designated independent live demand q_x opens once;
   Name/Return gives its PhiT front. A latent x retains its original future
   value fields; formation and Return do not execute those latent fields.
5. Original whole-argument checking and independent punctured-context assembly
   at this actual carrier/current tuple produce d_c. They are RT.3 inputs;
   origin/IF identity alone would not establish them. Eliminate **A_front**'s
   ActualAdm and complete P_F_apply^nat[S] family at H_diag for that same U,
   carrier and event. This supplies all actual receiver/pending/response/resume/
   result/future fields needed by the Call without an ordinary final a theorem.
6. The selected finite source Call/Bind rules independently compose the actual
   callee, inert carrier and raw U operation evidence. The selected ReadInvoke
   identity constructor then builds the R_c Phi(S).T front from the staged
   prefixes, actual receiver family and full guards. Native Strict composes
   the actual invocation-return/future maps, with no receipt replay or maker
   authority revival. Every extra arm retains its separate RT.3 contract.
7. Repeat at every actual later step demand and lawful capture restriction.
   The result provider from U_apply is its actual output (possibly another
   newly allocated step); its S value/world/future fields remain correlated.
   It is never replaced by s0 or a on the basis of descriptor equality.

These clauses give `S0_front : Phi(S).V(F_step,s0)` and the corresponding
source world, Name-carrier, body/return and pending-continuation fronts.
This uses the already constructed A_front universally; it does not invoke
RelativeBlock to obtain A_front or claim S0_front from an H_s0 leaf.

## 6. Exact unfinished postfixed obligation and falsifier

All actual s_i must receive their source fronts before S can be postfixed.
At the same source proof for s_i whose capture is arbitrary returned f_i,
the missing step is precisely a full checked front at F_c:

```text
non-hole B.V(A_f,f_i) -> Phi(B).V(A_f,f_i) -> Phi(S).V(A_f,f_i)
                                                     |
                                                     ? N_S
                                                     v
                                          Phi(S).V(F_c,f_i).
```

N_S must preserve every original actual decomposition, full challenge-domain
inclusion, guards, observation/result/provider/future maps and joint fields.
The ordinary final-model VIncl theorem is not that action. Positivity changes
the candidate relation at a fixed descriptor; it does not change A_f to F_c.
The non-hole returned-provider gap is unchanged and remains separate from the
successful conditional source-front order for a/s0.

If the returned tuple uses an exact H_s0 key, S0_front supplies its **native**
source readout. A different F_c still needs the original complete front
conversion, not H_s0 membership. A_front likewise stays native when H_diag
is absent. No common-descriptor choice is made by this attempt.

Thus the following are still unproved: full-domain RT.1 interpretation;
actual relative RT.3 checking/action/arm suppliers; H_diag when the native and
checked interfaces differ; and N_S for all remaining returned-provider uses.
Some added S.T tuples for those other inner Calls consequently lack their
Phi(S).T front. Listing them in S does not repair the deficit.

Conditional finishing step only: if those exact suppliers enable the same
source cases for **every** s_i and all their T/Car/W additions, every H value
has a source front and every other B component has its unfolded positive
front. Then S <= Phi(S) gives S <= M; alternatively S <= Omega_H(S) gives
S <= B, after which positivity maps the constructed fronts into Phi(B).
Neither inclusion is asserted here. Complete RT.2 and OuterNat remain open.

Falsifier for the local conditional lemma: under the exact supplied §2
contracts, one independently admitted actual source observation or future use
whose Strict/PureReturn/Bind/ReadInvoke clause requires a guard, original
field or output-front premise absent from the tables. In particular a result
clause demanding Phi(S).V(s_i) rather than its selected recursive S.V field,
or an early prefix requiring an already executed parameter/result, would
invalidate this derivation. A missing N_S does not falsify the local lemma;
it blocks the explicitly unfinished uniform postfixed step.

Failure conditions also include mismatched original roots/whole interfaces,
relative foreign certificates without embedding, final-only arm laws,
candidate-dependent admission, negative recursive fields, missing joint
guards, provider recombination or non-lawful live-event actions. No failing
challenge is removed. One bounded attempt stops at these owner clauses;
another inclusion/identity checker would not supply them.

## 7. Evidence, resources and frozen commit packet

One documentary clause derivation, no executable oracle. Source operations,
positive Phi clauses and RT.1/RT.3 are shared independent-contract assumptions;
a checker that assumes them would not validate their source meaning. No seeds,
ranges, mutation runs, probes, tests, builds, formatting, Git mutations,
children or questions. The only Git command was the assigned initial
read-only HEAD verification. Source reads and SHA-256 capture/recheck were
bounded; no whole-repository search was performed.

Unverified: all named suppliers, joint postfixedness, foreign/fixed-E embedding,
all-source adequacy, arbitrary recursive initialization/State, ordinary source
acceptance, principality, production/F5 correspondence and cutover. No
numerical CPU/RAM/wall-time cap was supplied; peak usage and total reasoning
time were not instrumented. Zero heavyweight processes were used.

Frozen dependency contents (SHA-256):

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
8a02c821a6b36486d613e5c44d1f96a5c6c0146d8bc4c8ebd99c032f422d4ea2  notes/theory/2026-10-08-outer-apply-closure-introduction.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f  notes/theory/2026-10-08-captured-call-closure-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
8158ebaccc43fc92297c4fe8a12a6dad10e21429cb279a7fe25b292b9577ecff  notes/theory/2026-10-08-rt2-relative-transfer-proof-attempt.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
```

Recommended next action: independently review the exact A_front then S0_front
clause order as a conditional local lemma; return N_S and full RT.1/RT.3 to
their original contract owners. Do not promote full postfixedness from this
construction order.

- Exact changed lease: `notes/theory/2026-10-08-rt2-joint-apply-source-front-attempt.md`.
- Baseline: `d2a21c4a6246173c906c0be9a1337160ea50409c`.
- Dependency changes: none by this lease; final hash recheck accompanies report.
- Review: unreviewed conditional research derivation; writes stop on handoff.
- Checks: initial baseline verification, bounded governing-clause reads,
  dependency capture/recheck and exact output inspection; no execution checks.
- Proposed message: `research: derive conditional joint apply source-front order`.
- Shared deltas left to primary/curator: record the conditional A_front/S0_front
  order; keep N_S, RT.1/RT.3, checked-interface correspondence, full RT.2 and
  OuterNat postfixedness open. No authority/task/index/theory-map/question edit.

Review repairs require a renewed explicit lease.
