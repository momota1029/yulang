# Original ordinary Call: open kernel contract candidate

Status: architect/compiler-referee reviewed research-only contract skeleton and conditional derivation
Gate: ORIGINAL_ASSOC, retaining CALL_TYPE and SIG_RULES prerequisites
Baseline: `5809cd94c346c6095189e0e0664a13457dea4a68`
Branch: `research/simple-sub-intrusion`
Write lease: this file only
Implementation authority: none

## Objective, method and result

Construct a candidate source/kernel contract for the five-node cut
`call(result(name f),result(name x))` inside exactly
`my apply f = { my step x = f x; step }`. The method is typed contract
construction: expose the required input/output sorts, complete observation
quantifiers, and licensing induction premises before proposing a rule head.
This is not another executable transition model or a source-clause absence
search.

The result is an **open contract**, not a complete candidate language meaning.
The source-to-core prefix is derivable under its named lexical interfaces.
Complete Call typing, an original slot/contribution introduction, and an
exhaustive original licensing grammar remain separate cuts. The approved
direction does not select the denotations needed to fill them. Completing
the skeleton by assigning arbitrary denotations would violate the assignment's
stop condition. No competing complete semantics or user-decision blocker is
established here.

Any newly proposed clause that changes acceptance, effects, licensing,
coverage, or the available original witnesses requires M3 independent review
and explicit recorded user approval before implementation. This note neither
requests that approval nor promotes the skeleton into Authority.

## Governing baseline and premise classes

Governing sections are FVIEW §§1.1–5, the exact integrated
`function-call-view-formation/q1 a2`, nested-block addendum §§1–4 and its
integrated `q1 a1`, typed-core §§6,9, source-contracts §§2.1–3.5, and DAG
CALL_TYPE/SIG_RULES/ORIGINAL_ASSOC/ATTACH/LIC_FORWARD/LIC_INVERT. The current
directional decision in `tasks/current.md` and directional addendum §§1–4
is retained. DAG entries and task text locate obligations; they supply no new
source semantics. Source-contracts' independently interpreted kernel and
descriptor inputs are conditional hypotheses, not approved completed rules.

| ID/class | Exact premise and source |
| --- | --- |
| A1, approved | For this candidate only, the block binds `step` sequentially and returns its value; inner `f` resolves to the outer formal, inner `x` to the local formal, and returned `step` retains that same outer capture. Nested §§1–3. |
| A2, approved | Relevant declarations/definitions/uses form one shared inferred contract; annotation absence gives the provisional fully protected Handler view; ordinary-value use can discharge that provisional role without changing an actual supplied callable's role/entry. FVIEW §§1.1–3; exact a2. No generic Value-entry-implies-Pure rule. |
| A3, approved | Original static `beta`/`Slots(beta)`, source scopes, paths, owners and receipts survive; a static slot differs from a receiver activation. One original `xi=(nu,K,D)` is shared; admission/formation are independent of `Q`. FVIEW §§2,5; a2. |
| A4, approved | A protected inferred variable's original upper exposure seeds only that upper `outEff(U)`; it does not seed an existing lower/provider occurrence or remove independently owned provider protection. Current task; directional §§1–4. |
| A5, approved | Source annotations, public schemes and internal evidence are distinct; callback-literal B, actual callable roles/entries, Option A/Option 2 and annotation-local permissions remain retained boundaries. FVIEW §§1–5. No production membership definition is supplied here. |
| D1, mechanically derived relative to lexical/interface premises | Given A1 and typed-core §6's ordinary parameter/Name rules, outer and inner formals have `Value(A_f)` and `Value(A_x)`, respectively. Name normalization returns those data; the local application synthesizes symbolic `Computation(E_fx,A_fx)`. |
| D2, mechanically derived relative to complete constructor interpretation | Typed-core §9 and source-contracts §3.2 expand complete invocation and Request/Bind suffix preservation. Their rules retain actual entry and designated consumer; they do not supply the independent descriptor typing lemma or original contribution sort. |
| P1, newly proposed proof input, unproved | A pointwise independent local descriptor/Call typing law over every admitted operand/world and complete output/pending observation, with no attachment in its premises. This is CALL_TYPE, not an approved rule. |
| P2, newly proposed semantic input, unselected | Independent meanings and introduction rules for the original kernel's slot ownership and complete contribution contract, joined on the original scopes and `xi`. No meaning of these objects is chosen below. |
| P3, newly proposed semantic input, unselected | The original kernel's coverage introduction and any rule assembling factored witnesses into the existing ORIGINAL_ASSOC complete-family witness. The original witness target is fixed; its source/kernel representation and assembly rule are not supplied. |
| P4, newly proposed semantic/proof input, unselected | Exhaustive original licensing introduction grammar and its source-origin/transport inverse, including conservative contributions and the inherited/annotated/generalized cases. |

The A rows are established decisions within their stated scope. The D rows
are conditional derivations using the named existing rules. The P rows are
candidate obligations, not established results. In particular A2/A4 do not
entail P2/P3/P4.

## Source prefix and complete callee/receiver accounting

Write `d_f,d_x,d_step` for resolved binders and `u_f,u_x,u_step` for their
uses. These are locators, not slot or contribution denotations. Under A1/D1:

```text
Gamma(d_f) = Value(A_f)       Gamma(d_x) = Value(A_x)
n_f = result(name f)         n_x = result(name x)
Result(Value(A_x)) = Comp(empty,A_x)
I_fx = Computation(E_fx,A_fx)
I_step = Value(Fun(Value(A_x),Comp(E_fx,A_fx)))
```

The empty row above belongs to the rebound ordinary Name result. It says
nothing about the complete external carrier received by `step`, a concrete
provider's body, or complete Function membership. Sequential binding and
the final `result(name step)` construct/return a closure without executing
the latent `f x` body.

For the complete relational Call retain both stages, at one original `X`
and `xi`:

```text
J_complete = J_f >>= S_receiver
S_receiver(actual_f,C) = ExecuteCallable_X(actual_f,Delay(J_x),C)
```

`ExecuteCallable_X` retains the actual provider identity, actual role and
entry, original environment/capture, receiver/receipt, current configuration,
body, designated result consumer, return delimiters and any independently
admitted adaptation. Its value-entry branch is:

```text
enter actual receiver; receipt;
Force_argument >>= (a,C'). typed rebind; body; designated consumer; return
```

The retained-computation branch binds the same carrier without that entry
Force. Neither branch is selected by the internal provisional Handler seed.
The latter is an inference-view fact, not actual provider execution metadata.

There are two required pending-suffix cases:

```text
callee pending:
  Request(q,C,k_f) >>= S_receiver
  = Request(q,C, (r,C'). k_f(r,C') >>= S_receiver)

receiver entry pending:
  Request(q,C,k_arg) >>= S_after_entry
  = Request(q,C, (r,C'). k_arg(r,C') >>= S_after_entry)
  S_after_entry = typed rebind; body; designated consumer; invocation return
```

These preserve request identity, origin, response port, raw continuation,
current resumed state and all joint dependencies. Resumption does not replay
receipt. A receiver body that is pure still does not justify dropping an
entry request or its pending suffix. The designated upper receiver view is
not the callee computation prefix; both remain in the whole Call contribution.

For the source-base ordinary Name evaluator, a separately adequate lexical
lookup yields `J_f=Return(actual_f,C)` and `J_x=Return(actual_x,C)` at this
point. It is then legal to simplify the source-base prefix using the Return
equation. This does not erase the stage distinction from the contract or
claim that Option 2 alternatives all have those source executions. Identity
of `Gamma` entries alone is not a complete lookup-adequacy theorem.

To finish P1, prove the local Call typing law at every independently admitted
operand/world assignment, for **all** complete returns, finite request
prefixes, raw-resumption developments and future uses of actual returned
handles. Each proof must retain compatible event-local extensions at the
original scopes. A proof of the equations alone establishes constructor
behavior, not `DescMem`. P1 must neither consume `OriginalAssocType_X` nor
admit an observation by assuming the membership it is intended to prove.

## Candidate kernel contract ports and exact introduction cut

Fix the independently interpreted original kernel `I_orig(X)`, original
`beta`, independently typed output position `p0`, source upper exposure `u`
and original `xi`. Let `a` range over the kernel's **existing** witnesses;
write its projections as `(s,c,w)` only if the kernel specifies them. These
names do not add sorts, witnesses, predicates or a new kernel implementation.

The proposed contract has the following open ports:

| Port | Required independently grounded content | Forbidden substitute |
| --- | --- | --- |
| Slot/owner introduction | How a source declaration/root and its original scope denote a static slot `s` in `Slots(beta)`, and how the typed position corresponds to `p0`. | `s=p0`, one slot per call, singleton inventory from one use, endpoint or locator equality. |
| Contribution introduction | What the original contribution `c` denotes; how it includes complete callee and receiver stages, original providers, pending continuations and dependencies. | `c=J_complete`, support-row union, body-only image, a fresh tuple declared typed. |
| Joint incidence introduction | How the previous two original objects and their witnesses are incident at `beta,p0,u`, at the same source scopes and `xi`. | Independently inhabited marginals combined later, Q success, solved Function shape, source-position equality. |
| Coverage | Which complete observations/challenges the original witness covers and with what quantifier order. | One reached event, no-return erasure, independently chosen `nu,K,D` per observation. |
| Licensing | Why that original incidence is licensed by its own original introduction/transport grammar. | Defining `Lic` to mean the desired attachment or supplying it as an opaque primitive whose inversion stops there. |

An assembly derivation would have this form, with every open port visible:

```text
A1-A5 + D1
    -> resolved source/upper exposure and normalized ordinary Call

independent operand/world interpretation + local P1 proof
    -> complete Call descriptor typing (no association assumption)

original slot/owner rule + original contribution rule
    + original joint-incidence/coverage rule (P2/P3)
    -> inhabited original association fiber retaining its existing witnesses

original source constructor correspondence + original licensing grammar (P4)
    -> Attach forward law and exhaustive licensing inverse
```

**Exact cut:** even after granting the local P1 proof, no selected rule joins
an independently interpreted original slot/owner to an independently typed
complete contribution and establishes their coverage at the original
`beta,p0,u,X,xi`. A4 supplies upper protection only. It does not fill any of
those three rule heads. Inherited provider protection remains a separately
retained arm, not a reverse instance of A4.

This skeleton stops before filling P2/P3. It does not define
`OriginalAssocType_X` by a fresh conjunction and then claim to inhabit it.
It asks for the original kernel's own introductions or an independently
proved correspondence into them. Nor does it restrict the result to a
chosen witness: every legitimate original arm and witness remains available.
The slot's identity persists across closure capture/read and fresh use;
an actual receiver activation may occur later and repeatedly, or never occur.
Dynamic activity can establish local receipt/visibility premises but cannot
generate the static inventory.

## Coverage forms and the fixed proof target

Use the already defined complete family `F_C(X;xi)`. A member `z` includes
its independently admitted challenge/world, complete observation or pending
prefix, and original stage/view incidence. This is notation for members,
not a new semantic Call index. Let `Cover_orig(a,z;xi)` stand for an
**unsupplied original kernel meaning**, not a predicate defined in this note.

The existing ORIGINAL_ASSOC target requires one original witness covering the
complete family. Pointwise coverage alone is therefore insufficient. The
following displays distinguish that fixed target from a possible factored
representation; they are not three interchangeable choices for the gate.

```text
pointwise:
  forall z in F_C(X;xi). exists a in I_orig(X).
      OriginalIncidence(a,beta,p0,u;xi) and Cover_orig(a,z;xi)

uniform complete-family witness:
  exists a in I_orig(X).
      OriginalIncidence(a,beta,p0,u;xi) and
      forall z in F_C(X;xi). Cover_orig(a,z;xi)

factored witness schema:
  exists an originally licensed source/transport derivation schema T.
      T retains beta,p0,u, original scopes and the same xi, and
      forall z in F_C(X;xi). exists a realized by T in I_orig(X).
          OriginalIncidence(a,beta,p0,u;xi) and Cover_orig(a,z;xi)
```

Neither pointwise choice nor an arbitrary set of all covering witnesses
provides the licensed derivation schema `T`. `T` can represent arbitrarily
long finite histories; this display does not impose a finite runtime-history
bound. All three formulas use the same original `xi`; none permits
`forall z exists xi_z` in place of it. Compatible local extensions retain
their original shared constraints and are not fresh independent ports.

**Conditional assembly lemma, not a semantic selection.** Suppose the
original kernel independently supplies a schema interpretation and assembly
rule which, from every required arm of one coherent `T`, constructs an
original `a_T`, retains original incidence, and proves
`Cover_orig(a_T,z;xi)` whenever the corresponding arm covers `z`. Suppose
the factored formula is established. For arbitrary `z`, instantiate that
formula to its arm and apply the original assembly rule. This proves coverage
by the same `a_T` for every `z`; incidence was retained by that rule. Hence
the uniform formula follows. Conversely the uniform formula implies
pointwise coverage by reusing `a`.

The assembly rule, its original existence, and its compatible shared-witness
premises are unproved. A union/product constructor on an unrelated relation
graph is not automatically such a kernel rule. This lemma identifies exactly
what would justify replacing factored coverage with one complete-family
witness; it does not adopt that replacement. Even an empty observation
family does not supply an original witness: uniform inhabitation still has
an existential premise. Static licensing cannot be discarded because an
invocation diverges or produces no outward event.

## Exhaustive licensing introduction/inversion obligations

No exhaustive original licensing grammar is specified by the approved
source direction. The following is a required last-rule accounting table,
not a claim that these rows are actual original rule heads or an exhaustive
definition. The unknown-rule row prevents a false exhaustive inverse.

| Possible original last-rule family | Introduction must establish | Inversion must recover |
| --- | --- | --- |
| Own source upper | Original protected-variable/upper witness, original static owner/slot, independently typed complete contribution and exact output incidence; no lower backflow. | That original source arm and all its slot/contribution/coverage premises, not just the protection seed. |
| Inherited provider/capture/read | Original provider-owned evidence and certified typed source map; captured `f` identity and complete contribution survive. | Original inherited input witness and lawful map; no newly invented own seed. |
| Annotation arm | Actual original annotation position and permitted contribution; permission and realized removal remain distinct. | Exact annotation/source boundary and retained unrelated effects/evidence. The exact candidate has no such annotation, but absence does not erase other original provider arms. |
| Generalized/fresh-use arm | Legal uniform freshening/graft/hiding at original binder positions with one joint witness and independently certified admission; no per-port hiding. | Original pre-transport licensed arm plus the precise certificate. Generalization eligibility is not assumed. |
| Mixed/shared-use arm | Original shared source formal/root and all required correlated use demands, retaining own upper and inherited provider witnesses. | Each required original arm and its common constraints; no marginal recombination. |
| Conservative licensed contribution | Original licensing and an independently typed complete contribution/admission certificate, including any licensed observation without a source execution. | Original contract/license origin and transport arm, not a source execution for every Option 2 observation. |
| Registered/recursive reference, if licensed | Registered original relation and the original finite-derivation or other supplied recursion principle; no generated fresh slot. | Its original premise/derivation principle, without silently assuming termination of arbitrary unfolding. |
| Unknown original rule | Its actual declared semantic head and premises. | **Stop:** no exhaustive licensing inverse until this branch is discharged by a pinned exhaustive grammar. |

Given that grammar and independently proved constructor correspondence,
LIC_FORWARD is induction on the actual attachment/source derivation using
the corresponding original licensing introduction at identical coordinates.
LIC_INVERT is induction/inversion on **every** original licensing derivation,
including its primitive kernel introductions, not merely the outer relation
graph. Its base cases must recover the original source/contract arm and its
complete contribution. Transport cases invert the exact original certificate.
All recovered witnesses are retained; no canonical witness is substituted.

This describes a conditional proof method. It cannot supply its own missing
base rule. Neither source-base C-realization nor ordinary Call typing proves
the exhaustive licensing grammar by assuming it as an input. Production
membership and admission remain independently interpreted, with Option 2
extras permitted; this proposal never defines them as the source image.

## Evidence independence, coverage and failure conditions

No executable experiment, Frozen Oracle lookup, random search, mutation
run, build, or test was performed. Seeds/ranges/process repetitions are not
applicable. The independent reference is pinned governing text for its
selected clauses; there is no independent executable semantic oracle.
This producer shares the primary's source interpretation, directional
decision and conditional kernel/descriptor assumptions. It does not claim
independent review of this output.

Coverage is exactly the assigned source, constructor and gate sections named
above, plus the directional decision and integrated answer bundles. Initial
batched context captures truncated; decisive source-contract §§2.1–3.5,
typed-core §§6,9, DAG entries and the current original-contribution frontier
were reread in bounded windows. This is not a whole-repository rule search.
Existing kernel-audit/direct-construction notes were consulted as retained
localizations; their attacks are not repeated or claimed as new results here.

Named failure conditions for the candidate contract are: P1 fails for a
complete pending observation; P2 cannot denote a jointly inhabited original
slot/contribution; a proposed factor assembly changes scopes or combines
incompatible witnesses; P4 omits an original licensing last rule; capture or
fresh use loses a provider/slot witness; admission depends on `Q`; a
conservative member is silently required to have its own source execution.
Any of these blocks adoption of the affected clause, not the selected
source meaning. A future checker supplied with P2/P3/P4 could test consistency
relative to them; it would not prove those are authorized source rules.

Unverified: complete descriptor/Call typing, actual fiber inhabitance,
complete Slots/profile/row inventory, exhaustive licensing, arbitrary
annotations, generalized/recursive source discharge, production parsing/HIR
acceptance, Option A/2 membership/admission conformance, all-world soundness,
source adequacy and principality. No gate closes. Repeating another image
composition or enlarging a transition toy model would leave P2/P3/P4
untouched; construction has stopped at that precise semantic cut.

Recommended next action: the primary should commission one concrete original
kernel rule package filling P2/P3/P4 with independently specified slot and
contribution meanings, explicit coverage quantifier/assembly law and an
exhaustive licensing grammar, then subject any outcome-changing additions to
M3 review and explicit approval. Keep the selected source meaning and
direction fixed while that package is researched.

## Checks, resources and dependency snapshot

Read-only checks: `git rev-parse HEAD`, `git branch --show-current`, bounded
`cat`/`sed -n`/`rg` reads; Python `hashlib.sha256` and byte comparison against
`git show 5809cd94c346c6095189e0e0664a13457dea4a68:<path>`. Both selected
question/draft/approved bundles (six files) matched committed baseline bytes.
The dependency table records the hashes before writing; handoff rechecks
them and performs note-local integrity checks on this exact leased path.

One research note; zero compiler/test/checker/build outputs and zero Git
mutations or children. At most six short independent read processes were
batched; no heavyweight process ran. No numerical CPU/RAM/wall-time budget
was supplied; process CPU, peak RSS and wall time were not instrumented.
There are no incomplete search shards or timed-out computations.

| Direct dependency | Baseline SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `tasks/current.md` | `c78c649542fda61aa74ca6460ace9cc1dc4f25a47b6a1d90294539a3aff33d12` |
| `tasks/research-lab.md` | `d8794543008221be430c3b676929b8601fb4534799fc67856e99ad140da0975d` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

## Independent review and integration revalidation

The architect reviewed the premise classes and original-witness target,
including a clarification that pointwise coverage is not an alternative to
the existing uniform complete-family witness obligation. The compiler referee
reviewed the conditional constructor/assembly reasoning, pending suffixes and
non-circularity boundary. Both reviews passed without remaining findings on
the candidate content at hash:

```text
f55bc37d80f835172aa796dfe691ad75a06f728cf5ba2daabd014b1cb04c343f
```

At integration HEAD `d8304f33b1adf62cf8645529e2a9c81281688e15`, all 17
declared dependency files still match their pinned baseline except
`tasks/current.md`. Its current hash is
`ad9e68c92307cb3b82cb57ea8f18065eae24b0988fc43dfbd3379947a5032b8d`; the
change adds only the bounded historical Pattern-boundary characterization and
the reviewed structural shadow Apply crosswalk. The source authority and
ORIGINAL_ASSOC frontier remain unchanged. The selected approved question
bundles still match their pinned committed bytes.

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-original-call-kernel-contract-candidate.md`.
- Baseline SHA: `5809cd94c346c6095189e0e0664a13457dea4a68`.
- Changed dependency hashes: only the navigation/status additions to
  `tasks/current.md` described above; no authority or gate change.
- Claim/review status: independently reviewed open research contract and
  conditional factor-assembly lemma; no complete rule, closed gate, or
  semantic/implementation authority.
- Checks already run: exact governing-section reads; dependency byte/hash
  equality; selected committed question-bundle equality; leased-note whitespace,
  link and hash-table integrity checks. No executable semantic checks or tests.
- Proposed one-line research-checkpoint commit message:
  `research: expose original Call kernel contract and coverage cuts`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  the contract ports and P2/P3/P4 proof cut from `tasks/current.md` and the
  ORIGINAL_ASSOC/SIG_RULES navigation records after adjudication. No new DAG
  edge, design-index status promotion, question bundle or authoritative rule
  change is proposed.

The producer stopped before review. The primary's post-review edits are limited
to the recorded outcome, the integration dependency revalidation and the
shared task navigation; they do not alter the reviewed contract reasoning.
