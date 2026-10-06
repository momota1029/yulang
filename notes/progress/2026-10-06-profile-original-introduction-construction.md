# Original-profile first introduction: exact-source constructor inversion

Date: 2026-10-06
Baseline: `167a5c2791abd8a5458554cf1ddbbb33f7f40b48`
Branch: `research/simple-sub-intrusion`
Status: frozen research-only producer artifact; independent review pending
Claim class: bounded source-rule derivation and precise proof blocker
Scope: `my apply f = { my step x = f x; step }`, original-profile P converse
Authority / implementation promotion: none
Exclusive lease: this file only

## 1. Objective, method and result

Attempt to derive

```text
Applicable_original(C,d_f,R_f,p;xi) => p=p0
```

by first-introduction inversion of the **selected source constructors**, rather
than defining applicability by a generated footprint. The attempt constructs
the source-role derivation with its open decorated premises, checks the
administrative normalization explicitly, and asks which last rule could
introduce a profile before transport starts.

The source rules determine the complete-invocation endpoint and the mandatory
`p0=(beta,call.effect)` seed. They also exclude treating the administrative
`eliminate(reify(call))` pair as an additional latent-result demand. They do
not produce the original profile needed by their decorated Call premise.
Inversion therefore reaches a **supplied profile operand**, rather than a
source rule whose conclusion exhaustively generates that operand. This does
not materially reduce `I-formal`, `I-call-rest` or `I-exhaust`. The lane stops
with that precise blocker; no new toy checker or larger enumeration is useful
for this attack.

There is no minimized source-valid counterexample and no impossibility result
for the eventual inference rules. The useful result is the explicit failed
proof step, including an administrative-consumer case that cannot repair it.

## 2. Governing premises and claim boundaries

The independently selected source meaning is the [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4: sequential local binding, final Name returning `step`, local `f`
resolving to the outer formal, and the same lexical capture surviving later
calls. No other brace meaning is considered.

[Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 fixes shared, Q-independent source formation; stable slot identity,
annotation absence and scope; the provisional protected Handler view and
ordinary-value refinement on one inferred root; and full protection/no
annotation grant at applicable unannotated positions. Its §5 explicitly leaves
the profile-producing judgment open. These policies do not themselves enumerate
the applicable positions.

The source-rule basis is [typed-core §6](../design/2026-10-02-typed-computation-core-elaboration.md)
and [typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md).
Their reviewed mathematical packages are conditional machinery, not new
language authority. [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3,10 fixes the decorated source-base boundary: profiles, typed paths,
owners and receipts are supplied; constructor-image correspondence and whole
transport operate on those inputs. Its exhaustive execution-clause accounting
cannot be repurposed as exhaustive raw-source profile introduction.

Retained reviewed research dependencies:

- [Call construction](2026-10-06-source-call-generation-construction.md) §§3–7:
  one shared `R_f,F_c,beta`, positive `ElimOrigin`, and `p0`; semantic Call
  constraints can be generated before satisfiability.
- [Profile source normal form](2026-10-06-profile-source-normal-form-construction.md)
  §§5–6: packet transport preserves origins; its original-introduction converse
  is open.
- [Formation-rule attempt](2026-10-06-formal-profile-formation-rule-attempt.md)
  §§3–5: only `Intro-Call-0` is established; `I-formal`, `I-call-rest` and
  `I-exhaust` are unknown leaves.

The [naturality note](2026-10-06-profile-substitution-naturality-closure.md)
is an **unreviewed research dependency at the pinned baseline**, used as a claim
to challenge, not as a source rule. Its one-node hypothetical result predicate
is not taken to be
source-valid, and its own earlier baseline is not silently substituted for
this assignment's baseline.

## 3. Explicit source derivation with open profile premises

Fix original scopes `sigma` and one joint `xi=(nu,K,D)`. Hypotheses for the
following bounded derivation are the approved resolution/capture tree, the
ordinary parameter and source-result rules of typed-core §6, and the reviewed
positive Call constructor. Endpoint satisfaction, full profile generation,
actual receipt realization and capture-packet attachment are not hypotheses
established here.

Generate the two ordinary formal interfaces before synthesizing the body:

```text
Gamma(f)=Value(A_f)                 Gamma(x)=Value(A_x)
n_f=result(name f)                 n_x=result(name x)
c=call(n_f,n_x)                    I_c=Computation(E_c,A_c)
```

The source application rule gives `d_c=reify(c)` and
`n_c=eliminate_p_c(reify(c))`. `p_c` is the application's known **outer**
computation port; it is not an effect path found inside an interpreted `A_c`.
The existing same-context delay/force law realizes this normalization as `c`
without moving execution across an entry or return delimiter. The complete
invocation relation owns `E_c`; it includes entry, body and designated
consumer, not only the callee body.

Synthesize the local closure, bind its returned value, and return its Name:

```text
I_step=Value(Fun(Value(A_x),Comp(E_c,A_c)))
n_step=result(lambda(x,n_c))
Gamma_after_bind(step)=Value(A_step)
n_return=result(name step)
n_block=bind(step,n_step,n_return)  // after administrative normalization
n_apply=result(lambda(f,n_block))
```

`A_step` is related to the actual local closure through the ordinary Bind
image; it is not an independently supplied provider. The formal `A_f` is
shared across the capture and callee Name; local generalization cannot replace
it by an independent provider. These are structural endpoint/role facts.
They do not assert completed schemes or typed packet attachment.

At the actual Call, the positive constructor supplies

```text
R_f,F_c; beta=(d_f,R_f)
ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))
p0=(beta,call.effect)
```

The remaining decorated Call premise includes the profile, receipt and typed
correspondence certificate. In the Call construction's §5 notation it is
`TypedCallCert_Dec(c,F_c,e;xi)`. That premise is explicitly **supplied** beyond
the generated initial incidence. Reconstructing Call from it proves the
decorated rule envelope, not the raw-source producer of its profile.

## 4. Administrative normalization cannot supply the missing origin

The following is a consequence of the supplied normalization rules, with
their existing typed/profile premises retained; it is not full source P.

1. For the callee, argument and returned `step`, the source interface tag is
   `Value`. Normalize constructs Result and introduces no elimination of a
   latent descriptor merely because that descriptor may later be inferred.
2. For the application, Normalize eliminates the known computation interface
   `Computation(E_c,A_c)`. The rule explicitly retains that interface's original
   profile and symbolic `K,D`; it does not construct a second profile inventory.
3. The delay/force realization uses the same computation/provider root and
   current context. Its consumer observes the complete outer invocation
   position already addressed by `p_out(c)`, corresponding to `p0` through
   `ElimOrigin`. It does not force a value returned at `A_c`.
4. If `nu(A_c)` has a Thunk or Function head, steps 1–3 are unchanged. A supplied
   result profile still follows its matching result correspondence. The
   normalization is not its first source introduction.

Thus counting the syntactic Force introduced by Normalize in addition to
the Call does not give a second original `beta` slot. Removing that
administrative pair does not prove that no separately supplied result-profile
origin exists. This distinction prevents a consumer-count argument from
silently becoming the missing first-introduction theorem.

## 5. Last-rule inversion and the exact blocked premise

The exact constructor audit is:

| Constructor seam | What inversion obtains | What it does not obtain |
| --- | --- | --- |
| Outer/local ordinary formal | `Value(A)` and fixed entry/rebind skeleton | Inventory of the inferred callback contract at `R_f` |
| Name/Result | Resolved provider/interface and matching existing packet | First source introduction of that packet |
| Local Lambda/capture | Closure/body/captured-root references; supplied packet transport | Original profile for captured outer `f` |
| Bind/final Name | Same returned provider/rebind witness and ordered suffix | New exhaustive original `beta` introduction rule |
| Call | Complete Function constraint and mandatory immediate `ElimOrigin` | Exhaustive profile operand of its decorated certificate |
| Normalize/administrative Force | Known outer interface consumption, retaining its profile | New result-descendant origin or profile inventory |
| Boundary introduction | Fresh dynamic boundary carrying its supplied signature profile | Constructor deriving that original static profile |

Start a proposed proof with an arbitrary original applicable witness. Invert
any already supplied transport steps by typed-boundary §6. Each relational
image output yields its input profile witness with the same source tag and
joint ledger. Receipt supplies ownership, not an original profile. If this
reaches the boundary-introduction rule, that rule takes
`b=(receiver,slot,Gamma,type endpoints)`; `Gamma` is an input supplied by source
elaboration. Its cardinality and dependent result positions are not produced
by the rule.

Attempting to invert **source synthesis instead** reaches the same cut one
level earlier: the ordinary formal rule produces `Value(A_f)`, while the
Call rule relates `A_f` to `F_c` with existing typed-path/contract obligations.
Neither conclusion states which original positions those obligations permit.
The positive `p0` witness passes through this cut; arbitrary original profile
witnesses cannot be inverted into that positive rule without an extra theorem.

The precise failed inference is therefore:

```text
source-role derivation above + decorated Call certificate
    => original Gamma has no introduction other than Intro-Call-0
```

Its missing premise is a source rule determining the **complete static profile
operand of that certificate** at `(C,d_f,R_f,F_c,sigma)`. The rule must connect
its introduction cases to the original source witness relation, including any
dependent result-profile schema, without using type shape or Q as the origin.
Neither generic descriptor well-formedness nor the supplied execution image
performs that connection.

`I-exhaust` is not assumed here. Consequently there is no theorem asserting
that the audit table is an exhaustive list of all lawful original profile
introductions. It is exhaustive only for the displayed source-role derivation
and supplied transport rules. Declaring those rows exhaustive for original
profiles would repeat the unresolved premise.

## 6. Challenge to the naturality limit and stop decision

The strongest possible objection to the unreviewed naturality note is that
source syntax fixes the only elimination, so a preattached dependent profile
at `A_c` should be ruled out by source inversion. Sections 3–5 test that
objection against the actual rule outputs. It fails: elimination locality
fixes runtime consumption and the mandatory immediate observation address;
the rules still retain a supplied profile operand. They do not contain a
first-generation locality clause saying that all profile schemas factor
through those elimination addresses.

This supports the note's preservation-only limit **for this inspected rule
basis**. It neither certifies its hypothetical dependent node nor proves
semantic underdetermination of every Authority-conformant completion. A
symbolic schema fixed before solving must still earn a source introduction;
stable identity and substitution naturality cannot earn it. Equally, no-source-
Force reasoning cannot disprove such an introduction solely from operational
uniformity.

The earlier transport inversion and this source-constructor inversion both
leave the same profile operand untouched. Stop this method here. Another
consumer-count proof, endpoint substitution example or transition checker
would not discriminate the missing premise.

Recommended next action: have the primary obtain one independently justified
local **original-profile introduction clause** for the exact unannotated
formal/Call seam, specifying whether it emits any dependent result schema and
proving its source-witness inversion. Review that clause against the selected
formation direction before using it. No new user decision or alternative
language meaning is inferred by this report.

## 7. Evidence, coverage and failure conditions

Method: manual source-rule derivation and last-rule premise inspection, for one
resolved source tree and arbitrary joint `xi`. There is no executable semantic
oracle, mutation campaign, random seed, range enumeration, compiler test,
build or production edit. Oracle independence means no legacy producer or
transition supplies a premise; it does not mean independent empirical
validation. Shared assumptions are the approved source tree and the supplied
reviewed decorated/source-role packages.

The administrative argument fails if normalization allocates an independent
original profile rather than retaining its input profile, if latent solved
shape changes the source tag, or if a consumer is reassigned to a different
port. Those changes are outside the inspected rules. The singleton remains
unproved if the missing source producer contains any independently justified
extra formal or Call-result origin, even with perfect transport.

Unverified: original contribution interpretation, seed/refined full-solution
preservation, all source forms, recursion/multi-use, arbitrary annotations,
typed capture attachment, actual receipts and receiver lifetime, admission A,
Option A/2 production alternatives, source acceptance, soundness and
principality. No `FVIEW -> SRC` edge or gate completion is claimed.

Checks already run: read-only branch/HEAD inspection; exact governing-section
reads; SHA-256 comparison of every direct dependency with pinned baseline
bytes; leased-note whitespace/link checks and final dependency recheck. No Git
mutation. At most six concurrent short read-only commands in the header pass;
subsequent derivation and artifact checks used one lightweight command at a
time. No Cargo or computation-probe wave or scratch output. CPU, peak RSS and
reasoning wall-time are uninstrumented. The assignment specified no numeric
reasoning budget; the explicit no-code/no-tests/no-build budget was respected.
Startup `tasks/current.md` capture was truncated; only its relevant P summary
was used, and no claim of complete task-record inspection is made.

Direct dependency SHA-256 snapshot (all equal to the pinned baseline bytes):

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-profile-source-normal-form-construction.md` | `ea32179888d41ceaddda7ba5c3566e1e83bf489da3fba763a28fda37e8876fad` |
| `notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md` | `8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b` |
| `notes/progress/2026-10-06-profile-substitution-naturality-closure.md` | `786d2e1cf070949556f557882fdbcc53eebc089cc537377877986bea722dc59a` |

Final live recheck detected unrelated HEAD movement to
`76fffec0edaacf56a9328ac50df2892fdbb4c24d` and a naturality-note delta. Its live
SHA-256 is `3c8f99d0456fb2becb57a6429407eb2fc7410ac5e27aaaa5c94cf81843112087`.
Read-only comparison with the pinned bytes shows a reviewed-status update and
one precision repair: excluding its particular `s1` does not exclude every
possible result schema. That repair agrees with this note's explicit
non-completeness boundary and changes no premise used here. All other direct
dependencies remain byte-equal. This artifact uses the pinned snapshot above;
it does not certify the live dependency's review. The primary was notified.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-profile-original-introduction-construction.md`.
- Baseline SHA: `167a5c2791abd8a5458554cf1ddbbb33f7f40b48`.
- Changed dependency hashes: no change to used pinned inputs; live naturality
  changed from `786d2e1cf070949556f557882fdbcc53eebc089cc537377877986bea722dc59a`
  to `3c8f99d0456fb2becb57a6429407eb2fc7410ac5e27aaaa5c94cf81843112087` as
  described above. Primary revalidation remains necessary before integration.
- Claim/review status: frozen, research-only bounded derivation and blocker;
  independent review pending; no original-profile theorem or gate closure.
- Checks already run: read-only baseline/dependency equality, targeted reads,
  leased-note whitespace/relative links, final direct-dependency delta audit.
- Proposed one-line checkpoint message: `research: locate exact original-profile introduction cut in source rules`.
- Shared-record deltas left for primary/curator: record this constructive
  source-inversion route as stopped at the supplied Call profile operand;
  preserve the administrative-normalization fact; leave `I-formal`,
  `I-call-rest`, `I-exhaust`, full P and all downstream edges open. Do not
  promote the unreviewed naturality node to a source-valid alternative.
