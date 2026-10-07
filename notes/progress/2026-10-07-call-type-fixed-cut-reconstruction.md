# CALL_TYPE: fixed-cut last-rule reconstruction

Date: 2026-10-07
Baseline: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
Status: frozen research-only premise-gap accounting; independent review pending
Method: reconstruct source judgments and inspect the required semantic last rule, without a supplied closure package
Exclusive lease: `notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md`
Semantic/implementation authority: none

## Objective and result

Try to derive ordinary typing of the complete inner Call in the approved source

```text
my apply f = { my step x = f x; step }
call(result(name f), result(name x))
```

from the recorded source clauses, keeping the original source kernel, binder
tree and `xi=(nu,K,D)`. The constructive prefix fixes names, source roles,
normalization, inert carrier construction and operational composition.
It does not produce a semantic descriptor last rule. The first unavailable
source-to-semantic step is lexical-context adequacy followed by Return
introduction. If actual callee membership is supplied as an operand premise,
that particular cut is discharged conditionally; whole-carrier admission,
phase preservation and complete pending-Bind typing still require their own
ordinary rules.

This is **bounded premise-gap accounting**, not a theorem, counterexample,
independent review, or semantic impossibility result. It adds an explicit
branch/cut reconstruction to the previous attempts; it does not supply their
conditional closure package or repeat the sorted-algebra separation.

The pinned DAG labels `CALL_TYPE` **OPEN-PROOF**, `DESC_CLAUSES` and
`ADMISSION_CLAUSES` OPEN-SEMANTIC, and `SEM_JOINT` OPEN-PROOF.
The task's semantic-gap description does not change these statuses.

## Authority and exact dependency scope

- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3 is Authoritative for this exact sequential binding, capture and returned
  inert local function. It supplies the displayed source cut and lexical identity.
- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§16–18 and 21 record user decisions: receipt before entry, whole-argument
  inert reification, one-layer demand, result forwarding, and outer-annotation
  parameter roles. Its document-wide Reviewed status supplies no additional authority.
- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5 is Authoritative for source formation direction and actual-role separation;
  it explicitly leaves the construction judgments open.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§1–4 records the direct user decision. Preserve upper-output protection and
  existing provider protection without back-propagating a seed into a lower effect.
  It supplies no event-level typing rule.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3,6,9 gives structural translation and the complete entry/body/consumer
  equations. Its header is Draft, Approved-by none. These constructions are
  used at their reviewed conditional scope, with their recorded source decisions.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2,3.1–3.5,10 is a reviewed conditional package whose concrete clauses
  remain Draft. §2.1 takes independently typed primitive and owner/view contracts
  as input; §2.2 requires constructor typing; §3.5 assumes local descriptor typing.
- The [DAG](../theory/successor-proof-obligations.md) CALL_REL/CALL_TYPE and
  DESC_CLAUSES/ADMISSION_CLAUSES/SEM_JOINT locate the gates; they are not source axioms.
- All six Oct 7/8 Call notes listed in the dependency snapshot were inspected.
  They already cover identity entry, rejected membership erasure, computed callee,
  conditional closure, sorted pending separation and structural correspondence.
  The source-generated theorem §§2.1–2.3 was inspected only to check whether its
  cited generator supplies a missing last rule: it also takes decorated kernel
  and primitive contracts as inputs.

No Oracle, implementation, successful comparison, or source-position identity
is used to infer semantic membership. The approved Option 2 remains unchanged:
source-base accounting does not decide all production-only alternatives.

## Fixed operands and constructive prefix

Fix one original source kernel `X`, lexical environment and provider roots,
binder tree, actual source/view incidences, and `xi=(nu,K,D)`. Let `h` be
any independently admitted operand/current-world assignment at those binders;
let `w` retain the original operation/provider/state/continuation witnesses.
The common interpretation is an explicit unsupplied `SEM_JOINT` premise.
No inhabitance of its admission domain is assumed.

Use `T[c]` for typed-core's executable translation, avoiding confusion with
the fixed source kernel `X`. For the exact ordinary formals, charter §21 and
typed-core §6 give the syntactic equations, relative to their lexical interfaces:

```text
Gamma(f)=Value(A_f)              Gamma(x)=Value(A_x)
d_f=name f                     d_x=name x
n_f=Normalize(Value(A_f),d_f)=result(name f)
n_x=Normalize(Value(A_x),d_x)=result(name x)
Result(Value(A_f))=Comp(empty,A_f)
Result(Value(A_x))=Comp(empty,A_x)

J_f=T[n_f]=Return(lookup f)
J_x=T[n_x]=Return(lookup x)
S_f(actual_f,Cf)=
    let t=Delay(J_x,original lexical references) in
    ExecuteCallable(actual_f,t,Cf;original complete view)
J_call=J_f >>= S_f
```

The source interface `Value(A_f)` does not specify the actual callable's role
or entry. Its use generates the existing Function and whole-argument obligations;
it does not solve them. The exact closure retains the same outer `f`.
`Comp(empty,A_x)` describes this Name source computation, including a latent
returned `A_x`; it is not a theorem that every carrier independently admitted
at the unknown receiver has this pure Name form.

The pointwise typing target remains

```text
for every original X,xi,h,w,O:
  fixed ordinary Call operand/world premises
  and raw J_call(h,O,w)
  => DescMem(R_call,O,w;xi).
```

It includes every independently admitted response/raw-resumption/future-use
development where the ordinary predicate requires one. Compatible local
extensions retain original coordinates and binders. No phase selects a fresh
replacement xi or independently hides a provider witness.

## First unavailable constructor rule

At the first Name/Return node, the structural rules establish only its source
interface and lookup identity. The semantic derivation requires the following
two last-rule conclusions, in this order:

```text
original independently valid lexical environment/current world;
Gamma(f)=Value(A_f); lookup f=actual_f
---------------------------------------------------------------- REQUIRED, NOT DERIVED
ordinary value/provider/world judgment for actual_f at A_f
with the original capture/dependent-provider incidences

that ordinary value/provider/world judgment;
the original Return relation yields O_f=Return(actual_f,Cf,w_f)
---------------------------------------------------------------- REQUIRED, NOT DERIVED
DescMem(Comp(empty,A_f),O_f,w_f;xi)
and the ordinary current-world/returned-provider consequences
```

These conclusions name required **sorts of existing judgments**, not new
predicates defined here. The inspected sources do not give an instantiated
lexical-context elimination or Return-introduction rule proving them.
The independent semantic predicates are not determined by `Gamma` identity.

If the stipulated operand premise already includes these facts, the first
two rows below are conditional inputs rather than additional missing laws
inside that stronger CALL_TYPE premise. This does not constitute a derivation
from raw names. The next unmet rule then occurs at Delay/whole-carrier
compatibility or actual receiver entry, according to which ordinary premises
are independently supplied. There is no globally first semantic cut independent
of that premise granularity.

## Branch-complete last-rule table for this reconstruction

In the table, `B_r` abbreviates the actual body plus its designated consumer;
`R_r` is only its existing remaining return shell. For Value entry,
`S_e(a,C)=original rebind; B_r >>= R_r`.
These are suffix locators, not added operations. An operation's declaration
consumer is kept separate from a closure's body consumer.

“Applies” means the listed structural/equational clause applies under its
recorded premises. Every semantic consequence in the last column remains a
required premise or rule until independently derived.

| Branch / occurrence | Applies: exact closed or conditional clause | Required semantic last rule / unsupplied premise sort |
| --- | --- | --- |
| Callee Name | Nested §2 fixes capture; core §6 gives `Gamma(f),d_f`; core §3 gives lookup | Lexical-context elimination yielding ordinary callable/provider and current-world facts; source tag alone is insufficient. |
| Callee Result/Return | Core §§3,6; contracts §3.2 Result inventory | Return introduction into independent `DescMem`, retaining latent callable future obligations. |
| Argument Name/Result | Same Name/Return clauses, at `x`'s own port | Value/provider/world lookup and Return rules at `A_x`; no callee witness substitution. |
| Inert whole argument | Charter §17; core §3 Delay; contracts §3.2 Reify/Call | Delay introduction and transport into the receiver's whole-carrier contract, plus the original argument-to-parameter compatibility obligation. This is `CarrierMem`/contract typing, not endpoint equality. |
| Outer Bind, callee Return | Contracts §3.2 `Return(f,Cf) >>= S_f = S_f(f,Cf)` | Typed suffix at the actual `Cf`; typed Bind/target-port preservation if required by the original rule. This reduces to receiver typing, not a new source proof of it. |
| Outer Bind, callee Request | Contracts §3.2 gives `Request(qf,C,kf >>= S_f)`; outside this exact ordinary-Name diagonal | Composed pending descriptor at the Call result, original request/response witness, current-world and independently admitted response/resume domain. Raw `kf` typing is insufficient. |
| Receipt/boundaries, any actual callable | Charter §§16–17; core §9 actual receiver expansion | Source-owned receiver/receipt/path and world preservation. Inference Handler seed does not certify the actual role or these judgments. |
| Value entry, Force Return | Core §9 plus Return-Bind yields `S_e(a,Ca)` | Whole-carrier elimination gives actual parameter value/provider/world facts at `Ca`; rebind preserves them; suffix is typed at the complete invocation port. |
| Value entry, Force Request | Core §9 plus Request-Bind yields `Request(qa,Cq,ka >>= S_e)` | Pending descriptor and every admitted development with rebind/body/consumer/return still pending. Receipt has occurred and is not replayed. |
| Retained-computation entry | Core §9 binds the same `t` without entry Force | Whole-carrier membership/transport at its declared view and body state. Purity, empty row or provider shape cannot replace this rule. |
| Closure body/native body Return | Core §9 retains `J_body` separately; contracts §3.2 Bind | Ordinary body-result/provider/world facts and typing of the actual remaining consumer/return suffix; `J_body=J_call` is unavailable. |
| Closure body or designated consumer Request | Request-Bind at that actual phase | Complete pending predicate for its continuation plus only the still outstanding consumer/return shell; original response/raw-handle/current-state incidence. |
| Operation native Return | Core §§3,9 native `MakeRequestThunk` return and native delimiter | Native returned thunk's ordinary judgment and declaration-consumer input contract; the native return does not establish the declared operation result. |
| Operation declaration consumer Return/Request | Core §§3,9 existing `Execute_decl_result`; Return/Request-Bind | Declared result/world preservation on Return; complete pending descriptor on Request with its existing remaining shell, no second native invocation. |
| Completed invocation/consumer Return | Core §9 and contracts §3.2 Result/Call | Outward descriptor and world/provider preservation through the original delimiters; actually returned latent providers retain independent future-use obligations. |
| Further resumption or future returned-provider use | Contracts §3.3 items 2–4 and §3.4 transport inventory | Independently typed response/current world, same original raw handle, or actually returned provider port; complete history preservation at the same jointly scoped family. The inventory is not its semantic discharge. |
| Other finite-prefix constructor or producer alternative | Contracts §§2.1,3.1–3.2 requires independently specified primitives/exhaustive accounting | Its actual constructor/typing rule and admission operands are unsupplied. No invented “other-prefix” transition, binary Return/Request exhaustiveness, or default descriptor acceptance is assumed. |

Return and Request rows cover every displayed Bind equation, Value and retained
rows cover the displayed entry alternatives, and closure/operation rows keep
their distinct consumers. The final row preserves the unknown branch.
Thus “branch-complete” means complete accounting for this displayed
reconstruction **including an unresolved catch-all**, not an exhaustive proof
for all Yulang observations or every production-only Option 2 member.

The suffix is never shortened: callee Requests retain construction plus
receipt/entry/body/consumer/return through `S_f`; entry Requests retain
`S_e`; body/consumer Requests retain exactly their remaining shell.
Completed phases are not appended again. Current resumed state and original
`K,D` stay joint. Membership in the whole Call does not reclassify a
callee-prefix event as receiver upper-output protection.

## Why the cited realization theorem cannot fill the cut

Contracts §2.2 defines `P_E` with both `M_E` and independently interpreted
`DescMem`. Inverting that conjunction establishes descriptor membership
only for observations already in the filtered bound. The required direction
starts from the raw generated observation and must show it survives the
filter. The text expressly demands a constructor typing lemma for this step.

Contracts §3.5 assumes those local descriptor lemmas before its induction.
Its induction cannot generate its own assumption at the Name/Return leaf,
the carrier/entry phase, or pending Bind. §3.3 lists four admission forms
but supplies no corresponding exhaustive world/carrier/response last rules.
§3.4 retains certified transport without introducing those missing semantic
premises; §10 explicitly leaves concrete clauses and complete coverage open.

No clause from the bounded inspected inventory resolves the first cut.
This is a localization of an unsupplied premise, not a repository-wide
nonderivability theorem. A future exhaustive ordinary clause family could
discharge it. This lane stops here: another transition checker or closure
package would leave the same premise untouched.

## Independence, coverage, omissions and checks

No executable checker, reference implementation or Oracle was used.
The reconstruction shares its operational equations with the cited candidate
core; it independently accounts for their typing premises only. Implementing
these equations in two checkers would demonstrate shared-assumption consistency,
not prove their source meaning or the independent descriptor clauses.

No seeds, enumeration ranges, mutations, builds, tests or performance samples
were run. Analytical failure conditions include: defining `DescMem` by the
source image, deleting the saved suffix, replacing current state with captured
state, weakening admission by Q, identifying native operation return with its
declared result, deriving actual Handler role from the internal formal view,
or treating the pure Name diagonal as all admitted whole carriers.

Checks performed: read-only `rg`/bounded `sed`/rule-file reads; baseline
HEAD equality; leased-path absence; SHA-256 and byte equality of all 15 direct
dependencies against the pinned revision. Early broad captures were truncated;
the governing target sections were reread in bounded extracts. No complete
repository search or proof-system mechanization is claimed.

Resource budget: static/proof work only, <=15 minutes; zero build/test/Oracle
processes and zero heavyweight processes. Read batches used at most six
short-lived lightweight processes. CPU and peak memory were not measured.
No scratch outputs, generated files or other research artifacts were created.

Unverified: actual independently admitted operand/world inhabitance; local
descriptor/carrier/world/admission specifications and their joint realization;
all response/resumption/future-history preservation; finite complete symbolic
invocation production; general recursive source formation; production-only
alternatives; original slot/contribution association and licensing; principality
and production conformance. No claim closes any of these gates.

Recommended next action: reconstruct or supply the original lexical-context
elimination and Return-introduction clauses with their independent
descriptor/world/returned-provider meanings, then adjudicate them as part of
DESC_CLAUSES/ADMISSION_CLAUSES before a CALL_TYPE typing induction. If those
facts are already supplied by the intended operand premise, identify that
exact clause and move directly to the Delay/whole-carrier and pending-Bind rows.

## Dependency snapshot

SHA-256 values below refer to baseline bytes; all matched working-tree bytes
at the pre-write check.

```text
a969662a9ba0d8e2256f4e8d8db8e4abd2b7f57380c461229ce0d1ca1a57036a unchanged tasks/current.md
1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3 unchanged notes/theory/successor-proof-obligations.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e unchanged notes/design/2026-10-02-typed-computation-core-elaboration.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 unchanged notes/design/2026-10-05-source-contracts-and-common-allowance.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed unchanged notes/design/2026-09-29-scc-intrusion-redesign-charter.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 unchanged notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0 unchanged notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 unchanged notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe unchanged notes/design/2026-10-04-source-generated-callback-structural-theorems.md
564deef056a8609fb570d7a4a17c33f0ee14d3d49c6eb7f87c1b1d91c3f0fa43 unchanged notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md
9e521a9543d0f523572b8f7e2f838b1ff63063385a239d651e85287e9f89f33f unchanged notes/progress/2026-10-07-call-type-local-law-falsification.md
0c87d266bdc76b061c5c9e09351723c7c1af4da8f3fca41abc1a4aa184c75dc9 unchanged notes/progress/2026-10-08-call-type-computation-entry-attempt.md
ab46864eb3639fb7dab81f42b756e94b2c0c6b958475e00bcdfa7a7264e6898e unchanged notes/progress/2026-10-08-call-type-closure-construction-attempt.md
9220be81922f3ac37a1540041b99e4123d0f314739b458b7086a67b6f02fe426 unchanged notes/progress/2026-10-08-call-type-pending-closure-falsification.md
de4b87744a9e791c2483c9fdd7f1f38354d17f223f71500f2196800764f7f172 unchanged notes/progress/2026-10-08-call-type-shadow-correspondence-audit.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md`.
- Baseline SHA: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`.
- Dependency hashes changed: all 15 matched before writing. Final recheck found
  only `tasks/current.md` changed to
  `6d52f842fefe36c77e7aa308b6f14781fbb22f245c263e00e36307f7282ab79b`.
  Its narrow diff changes the unrelated shadow State declaration-candidate
  follow-on record only; the CALL_TYPE frontier and all 14 other dependencies
  remain unchanged. Baseline source meaning and this reconstruction are unaffected.
- Claim/review status: frozen premise-gap accounting; independent review pending;
  no theorem, counterexample, semantic-rule adoption or gate relabel.
- Checks already run: governing/prior-note reads, baseline equality,
  leased-path absence, 15 dependency byte/hash comparisons; final narrow
  path/hash/integrity evidence accompanies handoff. No semantic execution.
- Proposed commit message: `research: reconstruct fixed Call typing last-rule gaps`.
- Shared-record deltas left for primary/curator: optionally link the explicit
  branch reconstruction and premise-granularity distinction; retain existing
  gate statuses. No shared task, theory, index, authority, question, code,
  manifest or lockfile change.
