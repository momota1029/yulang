# Identity inlet: inversion of the actual rebound Name carrier

Date: 2026-10-06
Status: bounded conditional constructor derivation; independently compiler-referee reviewed
Implementation authority: none
Baseline: `a4da1bf5fe22e0ab165c024a4101d227c62e35d4`
Lease: this note only; frozen on submission to the primary
Review: `compiler_referee` PASS, no BLOCKING/major/minor finding, on the frozen proof scope at SHA-256 `589fff827c98031131d386331d908253f7ef59e9de09d0aa17337532811dfde9`; review did not independently recheck Git dependency hashes

## 1. Objective, method and result

Revisit the ordinary caller of [initial admission construction §3](2026-10-06-independent-initial-admission-construction.md#3-separate-ordinary-caller-remove-the-formal-seed-retain-the-inlet):

```text
my id z = z
my caller x = id x
caller Unit
```

The distinguished argument is exactly `t_x = Delay(J_x)`, where
`J_x = result(name x)` reads caller's rebound parameter root. The outer
`Delay(result(Unit))` belongs to caller's inlet and is a different carrier.
This method inverts Name/Result/Delay and the dependent receipt/entry schema,
without executing a trace or choosing an inlet interpretation.

The new reduced fact is a conditional, current-state-parametric Return image
for **that lexical Name carrier**, together with its exact source-designated
received-carrier and result-rebind addresses. Its lookup is justified by
the rebound binding, rather than by substituting literal code for `J_x`.
No argument-side source tag or immediate port address remains to be guessed.
The first unsupplied step on this branch is the independent complete-inlet
typing/inclusion instance at the original `CarrierContract(F_id)`. Full
descriptor/profile/world/suffix validity and the stronger whole-interface
proposition remain open. This is neither a complete-row witness nor a
counterexample to source admission.

## 2. Sources, authority and explicit hypotheses

Checked governing sections at the pinned baseline:

- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§16–18,21: approved receipt-before-entry, inert whole-argument reification,
  Result forwarding and ordinary parameter tags.
- [Ordinary computation](../design/2026-10-02-ordinary-computation-semantics-package.md)
  §§2–3: current configuration, lexical argument environment, state-threaded
  bind, one receiver activation, designated Force and result rebind. This
  package is Draft; its selected source decisions are backed by the charter.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3,6,7 (actual receiver contract),9: Name/Result/Delay translation,
  synthesis, independent checking, full carrier-dependent invocation and
  whole-domain containment. These are reviewed conditional/Draft clauses.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2,3.1–3.5,3.7,5.1,8–10: active descriptor/admission interpretation,
  constructor inventory, local descriptor typing premises, independent
  histories, hard envelopes and retained provider predicates. Conditional
  research clauses do not become selected membership rules here.
- [Initial-context construction](2026-10-06-initial-context-source-construction.md)
  §§3–5,7–8, especially §4.4 and PCInit-source: one open tuple, generated
  Call receipt schema, independent WholeArgCompatible and world leaves.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6, introduction, transport and receiving-ownership clauses: indexed
  packets, no authority creation and actual receipt requirements.
- [Authoritative inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5 and committed approved answers for
  [inlet contexts](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md),
  [denotation A](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
  and [membership Option 2](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md).
  Full independent caller-context quantification and Q independence remain
  binding; concrete descriptor/admission rules remain open.

Read `tasks/current.md`, relevant `notes/design/INDEX.md` entries, the three
required repository rules, and the earlier [literal-carrier attempt](2026-10-06-return-carrier-inlet-construction.md)
to avoid repeating it. No Oracle mechanism or current compiler behavior is
used as semantic authority. The known id provider introduces no inferred
higher-order-formal seed in this ordinary route; this does not erase any
independently applicable original profile.

All statements retain the one tuple

```text
X_O = (sigma_O, xi_O=(nu_O,K_O,D_O), original roots and source identities,
       v_id, F_id, T_id=CarrierContract(F_id), all original typed packets,
       caller owner, current configuration C_0, complete view V_id,
       original consumers and ordered suffix).
```

Explicit hypotheses for the positive derivation:

1. The proposed Unit endpoint specialization is legal under the original
   component constraints. It is a candidate valuation, not a solved row.
2. At the actual post-entry caller configuration, the immutable parameter
   root `r_x` is bound to the returned Unit view `e_x`, with source interface
   `Value(Unit)`. Its original result-path correspondence, packet and legal
   scope are retained. The prefix's **independent typing** is a hypothesis;
   constructing its control graph does not establish it.
3. Use the written ordinary Name/Result/reify clauses and current-state
   interpretation. Typed packet transport uses its original supplied typed
   correspondences; equal endpoints do not supply missing correspondences.

The complete `F_id/T_id` interpretation, its local constructor typing laws,
complete profile and world validity are retained unsolved dependencies.
No hypothesis asserts Q, complete inlet compatibility, generalized-id
admissibility, or membership of the tested callable.

## 3. Proof tree and the additional source facts

Let `eta_a` be the lexical environment at `id x` after caller's actual rebind.
It retains `r_x -> (Unit,e_x)`. Every alias, delay reference and continuation
uses that same original binding, not a fresh Unit witness.

```text
original parameter rule and actual typed caller result rebind [hypothesis 2]
---------------------------------------------------------------------
Gamma_O(x)=Value(Unit); eta_a(r_x)=(Unit,e_x)
---------------------------------------------------------------- Name
I_x=Value(Unit); d_x=name(r_x)
n_x=Normalize(Value(Unit),d_x)=result(name(r_x))=J_x
---------------------------------------------------------------- Result
Result(I_x)=Comp(empty,Unit), with original r_x and packet references
---------------------------------------------------------------- Reify / source Call argument introduction
t_x=Delay(X[J_x], lexical eta_a references and original lineage)
ordinary data interface: Value(computation-data(Comp(empty,Unit)))
```

This is ordinary carrier-data synthesis under the stated hypotheses. It
does not derive membership at `T_id`.

Typed-core §3 gives `X[J_x]=Return(lookup(r_x))`. Consequently, for any current
configuration `C` allowed by the original world/entry interpretation and
using those retained immutable lexical references,

```text
Run(X[J_x],eta_a,C) = Return((Unit,e_x),C)
Force_argument(t_x,C) >>= S = S((Unit,e_x),C).
```

Here the equality retains the current-state component; the expression
cursor changes as ordinary execution proceeds. No store or activation
snapshot is taken from caller's earlier outer entry. This is a symbolic
constructor equation, not an executed silence test and not an assertion
that every graph-shaped `C` is legitimate. The parameter root is a value
binding; Name generates no consumer of a latent descendant.

With independently valid receipt/complete-view interpretation, §4.4's
source Function elimination separately fixes

```text
input(id x) -> F_id.received-carrier, with ORIGINAL t_x root;
output(id x) -> F_id.complete-call, within ONE original complete view;
receipt -> Entry(v_id:Value(Unit));
Force designated t_x port -> RebindResultPath(t_x,(Unit,e_x),C);
rebound z -> result(name z) -> designated consumer -> id return -> S_outer.
```

This identifies the dependent provider-parameter reference with id's actual
`z`, conditionally upon plugging that same provider. It generates no new
provider binder or boundary. Caller remains the surrounding owner during
this nested call; id's fresh invocation occurrence is distinct. Its normal
return removes that occurrence through the original return delimiter.

**Added precision relative to the prior notes:** the immediate lexical
lookup, state component and Force/Bind Return reduction are now derived for
the actual `J_x`, and the received-carrier/complete-call addresses come from
the written Function elimination schema. The prefix supplies `eta_a` and
`e_x`; the source constructors supply the image and address skeleton. The
complete descriptor kernel must still validate them. This removes neither
world typing nor original profile/inlet interpretation from the hypotheses.

## 4. Complete-carrier audit and the missing last rule

Status legend: **D** = derived structural/source fact under §2's hypotheses;
**C** = follows only after the named independent typing premise; **U** =
unsupplied semantic obligation. These are proof statuses, not Boolean
valuations of an alleged complete Yulang model. The table audits all required
factors; it does not invent a decomposition of `T_id` absent from the kernel.

| Required factor at the same original tuple | What the constructors supply | Status / remaining premise |
| --- | --- | --- |
| Whole argument/code and source tag | Exact `J_x`, Delay root, immutable `r_x/e_x`, `Value(Unit)` and Result interface | **D** under legal specialization and typed caller rebind; no literal-root substitution |
| Complete inlet descriptor and active provider predicates | The §4.4 emitted `WholeArgCompatible(Comp(empty,Unit),T_id;xi_O,e_a)` obligation | **U**: its independently interpreted complete inclusion/membership instance, with original active incidences; data typing does not identify `T_id` |
| Provider and complete Function descriptor | Same known `v_id`; actual Pure introduction, Value entry, body `result(name z)` and empty captures | **D** skeleton; **U** `WF_Dec(F_id)`, full provider membership, legal whole generalized use if required, and original complete bound |
| Inlet/output addresses, receipt and entry | Function elimination fixes the two immediate addresses and receipt-before-entry; actual Value entry fixes one designated Force and rebind | **D** schema; **C** actual typed receipt/rebind from original constructor-image laws; generating a schema is not a dynamic receipt certificate |
| Typed paths, complete view and full profile | Original indexes and packet references retained through Name/Delay; no new grant or merged alias view | **D** retention; **U** complete original position inventory and independent profile/constructor interpretation; **C** image transport once supplied |
| Current world and owner | Prefix/current `C_0`, lexical references, live caller and future id occurrence are structurally fixed; Return uses current state | **D** control/world skeleton; **U** independent environment/world validity and complete owner/activation typing; absence of imports/handlers proves no blanket permission |
| Origin, scope, authority and joint dependencies | Same source identities, sigma_O, one xi_O and all K_O/D_O references; no source operation or capture grant introduced | **D** preservation; **U** satisfaction of every original active predicate; retained constraints are not asserted true |
| Result, consumer, return delimiters and surrounding suffix | Exact ordered rebind/body/consumer/id-return/caller suffix; Return/Bind unit reduction above | **D** code/order; **U** independently typed complete suffix/image bound and current-state dependencies; conditional transport cannot introduce validity |

At this particular argument-side branch the missing last rule is therefore

```text
Name/Result/Delay derivation in §3;
original T_id/F_id interpretation, full indexed descriptor/profile/world/
provider/suffix side conditions at sigma_O under the SAME xi_O
??????????????????????????????????????????????????????????????????????
complete inlet typing/inclusion for this original carrier interface,
including actual t_x,e_a,C_0 at F_id.received-carrier.
```

The source-contract §2.2 constructor typing lemma is exactly where generated
images must establish independent `DescMem`; §3.5 assumes those lemmas. The
Call rule in initial-context §4.4 emits whole compatibility as a side
condition and does not introduce it from the reify row. Its required original
provider/admission predicates cannot be replaced by bare payload equality.
This is the first unsupplied constructor premise **on this argument branch**,
not a claim that other Call premises have been proved or have a universal
evaluation order.

A concrete inlet certificate for `t_x` would validate that challenge only.
The emitted whole-interface proposition retains its complete semantic
quantification and cannot be proved by one returned observation. Likewise,
PCInit-source requires X_O to satisfy the local relations: using its
conclusion to supply this missing side condition is circular. The caller
prefix is itself typed only conditionally; its normal control reduction
cannot be used as independent proof that the outer inlet or inner inlet
already satisfies the same missing complete-descriptor conditions.

Thus neither the stronger WholeArgCompatible proposition nor an admitted
initial tuple is constructed. No source impossibility is established.

## 5. Independence, failure conditions and next method

This derivation depends on the written source constructors and accepted
source/control decisions, independently of Q and Frozen Oracle. It shares
their explicit typed-rebind, legal assignment, descriptor, profile and world
premises. There is no second executable oracle. A checker assuming the final
inlet rule would check that assumption's consequences, not prove the rule.
No seed, range, finite enumeration, numerical experiment or mutation run
exists in this lane.

Discriminating logical mutations, not run tests:

| Mutation | Failure condition |
| --- | --- |
| Substitute outer literal carrier for t_x after equal Unit lookup | Loses original code/root, lexical source position and packet references |
| Treat retained eta_a as a snapshot of store/active frames | Contradicts ordinary current-state Delay/Force equations and charter §17 |
| Infer T_id membership from Value(Unit), Result empty, or Return image | No independent complete descriptor/inlet introduction rule is supplied |
| Use separately chosen xi or e_x for the Force, z and suffix | Breaks the original whole-tuple dependency and packet identity |
| Omit profile/world/suffix predicates because this code has no request node | Drops required complete admission constraints; absence of events is not permission |
| Identify the body/result skeleton with F_id or restrict T_id to t_x | Replaces the complete bound or independent challenge domain |
| Invoke PCInit-source/Q to prove its local inlet antecedent | Assumes the Q-independent admission premise being sought |

Two earlier routes already reached this inlet premise. This Name-specific
inversion reduces structural uncertainty but leaves that same semantic cut
open. Another identity trace, a larger Return-only checker or a silence probe
would not progress it. Recommended next action: locate the independently
interpreted complete Lambda/inlet constructor clause and its original active
provider/admission factors, then instantiate its Name/Return carrier case
using §3's exact roots and one xi_O. If no such clause is supplied, record
that dependency explicitly; this note proposes no rule or user choice.

## 6. Checks, omissions and commit packet

Checks run: read-only `git rev-parse HEAD` and narrow `git status`; bounded
`rg`/`sed`/`cat` source reads; SHA-256 of pinned `git show BASE:path` contents
compared with current bytes for the dependencies below; note-local path,
whitespace and lease checks. Some combined output was truncated; the governing
clauses and omitted current-task slice were reread in smaller captures. No
exhaustive repository search for an unnamed alternative kernel clause is
claimed. Verification is producer inspection, not independent review.

Resources: at most four lightweight read processes in a wave, no heavyweight
process, builds, tests, Oracle execution, checker, performance measurement,
child agents, Git mutation or background jobs. CPU/RAM peaks and precise
wall-time are unknown. The only output path is the leased note; no resource
budget expansion was made.

Unverified: original-row/nonempty completion existence, independently typed
caller prefix, original F_id realization and generalized use, full inlet
compatibility, arbitrary worlds and challenges, requests/resumptions/future
uses, production-only members, recursive inference, principal inference,
production inclusions and compiler acceptance. These omissions neither
exclude those cases from the language nor establish failure.

Commit packet:

- Exact leased path: `notes/progress/2026-10-06-identity-carrier-inlet-construction.md`.
- Baseline SHA: `a4da1bf5fe22e0ab165c024a4101d227c62e35d4`.
- Dependency changes: none at producer recheck; all listed baseline/current
  bytes match. Unrelated branch movement requires only dependency revalidation.
- Review status: unreviewed bounded conditional research; writes stop before
  submission; no independent review, admission result or implementation authority.
- Checks already run: scoped constructor/quantifier/carrier audit, pinned/current
  dependency hashes, note whitespace/link/lease checks; no build/test/probe.
- Proposed commit: `research: invert actual identity Name carrier inlet`.
- Shared deltas intentionally left to primary/curator: record the conditional
  exact Name-carrier Return image and immediate Call-address derivation; retain
  the original complete-inlet constructor/inclusion, typed prefix/world,
  profile and suffix obligations as open. No shared-record or authority change.

Frozen source dependency hashes (SHA-256; current bytes match baseline):

| Dependency | Hash |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `tasks/current.md` | `a79f33ae8be378516fb2fabf5fe4127617111f66382699f1b2c2fc5fb24d24bb` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/progress/2026-10-06-independent-initial-admission-construction.md` | `4feb8131e9360ba8508b0eace82d882e446433d5b5f75beee402027e4986284f` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `notes/progress/2026-10-06-return-carrier-inlet-construction.md` | `e46235b6962f32032dca76f21dbabcde9d6a1e9f55d9809fe4359bcc39d400ae` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
