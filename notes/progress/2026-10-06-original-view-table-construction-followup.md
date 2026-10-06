# Original view table: constructing the contribution before attaching its slot

Date: 2026-10-06
Baseline: `843f78ccaae0eac1a49838b54cf2a3863aa0b8a9`
Branch: `research/simple-sub-intrusion`
Status: frozen unreviewed bounded research; no semantic or implementation authority
Method: one structural constructor derivation, then one explicit inversion check
Exclusive lease: this note only

## Objective and result

For the approved exact source

```text
my apply f = { my step x = f x; step }
```

attempt to replace the original profile part of `TypedCallCert_Dec` by source
construction of the complete `(slot, signature occurrence, contribution,
scope/dependency)` table on one whole row `X` and `xi=(nu,K,D)`.

The ordinary constructors construct a finite **complete-invocation relation
template** for the single source Call. In this exact source, the callee prefix
is a returning Name computation, so it can be eliminated by the ordinary Bind
unit equation. The remaining template is the same captured provider's actual
entry/body/designated-consumer/return image on the delayed returning Name `x`.
This is stronger than merely pointing at `p0`: it provides the source operand
and control structure that a contribution attachment would have to interpret.
It remains parametric in independent provider/view/world contracts.

The first unsupported constructor premise is the attachment of that template
to an original static slot at the signature occurrence, with a complete
contribution typing certificate and exhaustive original attachment inversion.
An operational template is not already a licensed decorated table entry.
Consequently the profile part of `TypedCallCert_Dec` has not been replaced.
This is a bounded proof-composition obstruction, not a source impossibility,
an admitted counterexample, or a reason to reopen the selected source meaning.

## Authority, hypotheses and claim classes

Governing sections read directly:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5 and integrated [q1/a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md):
  shared source-driven contract, stable original slots/scopes, Q independence,
  internal seed versus actual callable role, detailed formation still open.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3,6,8–10: independent whole-tuple primitive/descriptor/owner kernels;
  source Call inventory; conditional source-base correspondence; retained
  Option 2 extras; allowance coverage does not construct source applicability.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: original protected-variable upper output, no lower backflow, and
  introduction witnesses distinct from static slots. Its direct user decision
  governs its scope; proposed notation remains Draft.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3,6: Name/Result/Lambda/Bind/Call structural construction, ordinary
  Value-entry skeleton, provider-owned complete invocation.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6: independently supplied source signature profiles; indexed packet
  transport; matching observation/receipt/live receiver required for incidence.
- [Exact nested meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: sequential local closure binding, inert return of step, same outer
  capture. It decides only this exact brace form.

The three assigned predecessor constructions and source-call construction
are reused conditional research. Their producer checks and independent
reviews do not promote their still-open premises to source rules. The
Frozen Oracle signature archaeology is historical comparison only: its
source-demand origin, frame/formal grouping and downstream shape fold suggest
three separate operations, not a current semantic grouping or slot rule.

Fix the original binder tree, lexical references and a candidate whole `X`.
`X` contains the original upper demand `U`, providers, carriers, world,
continuation, consumers, all signature coordinates and the same `xi`.
No complete or admitted solution is presumed. Logical witnesses remain
under their original rigid dependencies. Hypotheses are:

```text
H1: approved exact core correspondence and resolved lexical identities;
H2: typed-core constructor equations and source role/consumer skeletons;
H3: independently interpreted complete provider execution primitives;
H4: original seed and same-root seed-at-upper-exposure witness;
H5: independently typed packet/owner correspondences, only when transporting
    a supplied decoration or interpreting an actual execution.
```

H3 does not certify a provider or world chosen arbitrarily for `X`. H5 does
not construct the original profile. H4 uses the previously derived source
exposure; this note does not reprove full seed/refinement solution preservation.

Claim classes:

| Class | Claim |
| --- | --- |
| Established dependency fact | All 15 direct inputs match the pinned baseline bytes |
| Bounded characterization | Exact ordinary constructor outputs and the first unsupplied attachment premise |
| Conditional derivation | Complete Call template expansion and its finite constructor inversion under H1–H3 |
| Candidate assumption, not used | An original attachment law whose two coverage directions would complete the table |
| Not established | Complete table/profile, complete-row nonemptiness, initial/history admission, source adequacy, principality, production conformance |

## One constructive route

Use the approved core with distinct original labels:

```text
L_apply = lambda(d_f,
  B_step = bind(d_s,
    R_step = result(L_step = lambda(d_x,
      C_fx = call(R_f = result(N_f = name d_f),
                  R_x = result(N_x = name d_x)))),
    R_out = result(N_s = name d_s)))
```

The previously established 11-node inventory is retained: two Lambda, one
Bind, four Result, three Name, one Call. This route constructs their relation
templates rather than inferring a slot count from that inventory.

Let `rho_x` be the step body's lexical environment. H1 fixes `rho_x[d_f]`
to the same captured outer binding, and `rho_x[d_x]` to its actual rebound
argument. Lookup may carry a supplied typed packet; it does not construct
its original applicability. With current configuration `C`, H2 gives:

```text
J_f = X[R_f] = Return(lookup(rho_x,d_f), C)
J_x = X[R_x] = Return(lookup(rho_x,d_x), C)
t_x = Delay(J_x, original lexical references)

X[C_fx] = J_f >>= (lambda v. ExecuteCallable(v,t_x))
         = ExecuteCallable(lookup(rho_x,d_f),t_x)
```

The equality is the ordinary `Return(v,C) >>= S = S(v,C)` law with the same
current state and provider. It removes only the administrative callee Return
prefix. It assumes no execution of `t_x` before receipt and does not remove
the provider's own entry, result consumer, invocation delimiter or evidence.
If checking uses an executing adapter, its independent conversion bridge is
an additional premise; the representation-preserving derivation here does
not silently insert that adapter into `J_f`.

Write `T_C` for this expanded **existing constructor image**, not a new
primitive or inferred interpretation:

```text
T_C(X) = complete finite-prefix/development relation of
  ExecuteCallable(lookup(rho_x,d_f),
                  Delay(Return(lookup(rho_x,d_x))), U,
                  actual entry, designated consumer, current world; xi).
```

Actual receipt precedes entry. If the actual provider has Value entry, the
whole delayed Name computation is forced once and its result is rebound;
retained entry stores that carrier. Provider body and designated consumer
then run in their specified order. Requests retain the original raw handle
and unfinished suffix; resumption uses current state and never replays receipt.
These are H2/H3's existing complete invocation clauses. They cover suspension,
nonreturning prefixes and returned latent providers, and do not require every
carrier to return. The formal's source-specific `NonHandlerFormal` inference
does not rewrite the supplied provider's actual role/entry.

The outer constructors also have explicit templates:

```text
V[L_step] = Closure(Value(A_x); X[C_fx], captures={same d_f reference})
X[B_step] = Return(V[L_step]) >>= (lambda s. Return(s))
V[L_apply] = Closure(Value(A_f); X[B_step], original lexical references)
```

Each closure's Value entry skeleton is generated before its body. Creating
or returning `L_step` does not execute `C_fx`. Its later invocation uses the
captured reference retained above. The Bind unit simplification is an ordinary
source computation fact and supplies neither a public capture field nor a
new beta-owned signature position.

The source-only proof tree is therefore:

```text
ordinary formals -> Value(A_f), Value(A_x)
resolved Names -> same provider references -> four Result templates
Results + H3 -> C_fx complete invocation template T_C
C_fx + Value(A_x) + capture reference -> inert L_step
L_step + Result + sequential Bind + Name step -> returned step
returned step + Value(A_f) -> inert L_apply

seed H4 + original Gen-Call-0 demand U
  -> beta=(d_f,R_contract), p0=outEff(U), ElimOrigin(C_fx,u,...,p0,p_out)
  -> a0=(k,beta,u,sigma_x,p0), directional protection, no beta grant
```

All references and generated obligations remain in the original scope tree
and share `xi`. This constructs a source-labelled complete contribution
**template** and the known upper occurrence. It does not instantiate full
descriptor/provider/world satisfaction or original slot attachment.

## Proposed table row and every open leaf

The desired row has the shape

```text
(s, (u,p0), T_C with complete typing/owner/view certificate,
 original sigma_f -> sigma_x capture and shared xi dependencies).
```

This is a partially filled target, not an emitted table entry. The relevant
certificate tree has the following explicit leaves:

| Leaf | Available source output | Remaining obligation |
| --- | --- | --- |
| Original static slot attachment | `beta`, upper use `u`, `p0`, ElimOrigin, a0 | Produce source-owned `s` and its association with this original occurrence/contribution; prove attachment inversion and exhaustiveness |
| Complete contribution interpretation | `T_C`'s same-provider/carrier/control template | Independently certify descriptor membership, complete view/owner incidence and original provider/world predicates for the attached contribution |
| Complete source call checking | Generated `WF_Dec(U)`, `VIncl(A_f,U)`, whole `J_x` compatibility, complete image inclusion | Satisfy them jointly on X; emitting them proves no solution |
| Original profile portion of `TypedCallCert_Dec` | Mandatory tagged upper delta and no-annotation policy | Supply the complete original table, including every licensed case and indexed inherited packet inputs |
| Remaining decorated certificate inputs | Conditional transport/receipt/observation structure | Derive or independently supply actual typed receipt, owner, observation and operation witnesses at their incidences |
| Complete initial and future domain | Original source/control templates | Independent initial argument/import/world admission and all permitted developments; not obtained from one returning run |

The first leaf concerns a static signature constructor, before actual event
receipt/observation or history closure. The template makes its operands
concrete; it does not give its missing licensing clause. Source-contract
§3.5's exhaustive inventory theorem cannot substitute for that clause:
its source base already has independently typed owner/view kernels and
complete alternative accounting as premises. Production extras are also
retained at independent leaves, rather than required to have source bodies.

## One explicit inversion check

First invert a **template derivation**, using H2 and retained source labels.
An `X[C_fx]` root has last constructor Call and ordered operands `R_f,R_x`.
Each operand inverts to Result then to its resolved Name. The callee Name
recovers the captured `d_f` reference; the argument Name recovers `d_x`.
The enclosing Lambda/Result/Bind/Name sequence recovers `L_step`, its
capture and the inert return. Neither duplicate dynamic activations nor
equal endpoint assignments alter these original labels. This is exact
inversion of the finite template, conditional on its constructor derivation.
It is not inversion of arbitrary observations to source bodies of a provider.

Now start from an arbitrary purported original table witness
`r=(s,t,T,sigma,D)` on the same X and demand inversion to that tree.

1. If `r` is an indexed transport result, typed-boundary §6 recovers its
   original input witness and matching path. If the arm is inherited
   provider/result evidence, inversion ends at that independent input and
   does not create an own-beta row. A repeated activation may carry the same
   static beta with a different original boundary/receiver; beta equality
   alone cannot choose the arm.
2. For the own-introduction arm, transport inversion reaches the original
   supplied signature profile. The profile's slot/signature/contribution
   attachment must now invert to a source constructor.
3. Neither the Call template equation nor `ElimOrigin` has that profile as
   its conclusion. Dir-Protect yields the known directional witness, but
   has no exhaustive conclusion about all profile/attachment constructors.
   `WF_Dec`, comparison and independent admission check an original
   decoration; their successful witnesses do not allocate its source slots.
4. Therefore inversion cannot conclude `t=(u,p0)`, `T=T_C`, or the original
   source-owned slot witness for **every** own-beta table row without the
   missing attachment law. Shape folding or historical frame grouping cannot
   supply it. Conversely, `T_C` plus a0 does not construct a licensed table
   row without forward attachment and complete contribution certification.

The two requested coverage directions both stop at this same constructor
boundary:

```text
source Call template + original upper witness
    -/-> licensed complete table row          [forward attachment open]
licensed own-beta complete table row
    -/-> source Call/upper constructor tree   [exhaustive inversion open]
```

This does not assert additional applicable rows, declare their absence, or
set `Slots(beta)` to a singleton. The inspected composition does not prove
the required equivalence. No claim is made that a future construction cannot
derive it from stronger existing source judgments. The predecessor attempts
already left this premise open; another checker of the template equations
would leave it open again, so this lane stops here.

## Independence, discriminators, checks and omitted scope

No Oracle transition rule, frame selection, marker group or projected fold
is a premise of the proof. Oracle origin/group/fold are only a historical
lead for separating template generation, attachment and representation.
H2/H3 are shared with the predecessor proofs; this source expansion is not
independent validation of their semantic correctness. A checker implementing
the same equations would prove only conditional consistency of those rules.

Logical mutations, not executed tests:

- Replace the returning callee Name by an effectful computation: the Bind
  unit reduction fails; the callee prefix and its pending suffix must remain.
- Assign a lower/provider output mark from endpoint equality with p0:
  original upper provenance is lost and selected no-backflow is violated.
- Replace complete `T_C` by outward support: entry, consumer, suspension,
  owner/receiver and current-world predicates disappear.
- Drop indexed source witnesses: own introduction and inherited packets,
  including different activations of the same static beta, become conflated.
- Close the table by `{a0}`: forward attachment and exhaustive inverse become
  an assumed closedness rule rather than a source derivation.
- Freshen xi or its provider/world witnesses independently per table entry:
  the one original shared assignment and dependencies are destroyed.

Commands/results: bounded `cat`, `rg`, `rg --files`, `sed -n`; read-only
revision/branch/status checks; Python SHA-256 and byte comparisons using
`git show <baseline>:<path>` for 15 direct inputs; note-local whitespace/link
and dependency checks at freeze. All direct inputs matched the pinned blobs.
Some combined captures truncated; decisive constructor/profile-input clauses
were reread in bounded captures. No absence claim relies on truncated output
or a repository-wide search.

No tests/builds/checker/Oracle execution, numerical seeds/ranges, executable
mutations, scratch output, formatting, Git mutation or child delegation.
Coverage is the exact 11-node ordinary source template and its one structural
inversion attempt. Resource use: lightweight reads/hashes only, zero heavyweight
processes, one leased output. No numerical CPU/RAM/wall-time limit was supplied;
aggregate CPU, peak RSS and elapsed wall time were not instrumented.

Unverified: arbitrary braces/annotations/adapters, recursive source formation,
generalization/use completeness, signature-slot association, original full
dependency formation, complete profile/descriptor/world satisfaction, all
carriers/histories, completion nonemptiness, principality, source adequacy and
Option A/2 production conformance. The note neither proves source rejection nor
finds two authority-consistent meanings with different admitted observables.

Recommended next action: inspect and expand the original source Function
signature attachment judgment at beta introduction, requiring its actual
independent clause to connect `T_C`/`(u,p0)` to a static slot and invert every
own-source table row. If that clause is absent, return that exact rule gap to
the primary rather than run another image/support/template checker.

## Frozen dependencies

SHA-256 values describe baseline inputs, not authority or review of this note.

| Direct input | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |
| `notes/progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `1621abe333739b475222953ec52adfd5a67d54727c2b612bdee160186ede8b30` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-original-view-table-construction-followup.md`.
- Baseline SHA: `843f78ccaae0eac1a49838b54cf2a3863aa0b8a9`.
- Changed dependency hashes: none; all 15 direct inputs match baseline blobs.
- Claim/review status: frozen unreviewed bounded characterization and conditional
  source-template derivation; no theorem closure, Oracle authority or production
  authorization. Producer checking is not independent review.
- Checks already run: governing-section reads; structural constructor and
  explicit inversion audit; same-provider/xi/scope and complete-contribution
  audit; 15 dependency byte/hash checks; note-local link/whitespace checks.
- Proposed research-checkpoint commit message:
  `research: expand original Call contribution and locate slot attachment cut`.
- Shared-record deltas intentionally left for primary/curator: distinguish
  constructed complete Call relation template from licensed original table
  entry; record static signature-to-slot/contribution attachment and exhaustive
  inversion as the exact residual; keep full profile, same-row nonemptiness,
  admission, principality and production gates open. No shared task/index/theory,
  authority, question bundle or code file changed. Writes stop at submission.
