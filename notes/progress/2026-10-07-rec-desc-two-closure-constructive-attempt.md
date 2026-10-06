# REC_DESC: constructive two-closure introduction stops at the root rule

Date: 2026-10-07
Assigned baseline: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`
Status: compiler-referee reviewed research-only derivation prefix and bounded source-rule blocker; no blocking/major findings
Gate / method: REC_DESC / ordinary constructor introduction for the actual K knot
Authority: none for a semantic rule, interpretation choice or implementation
Exclusive write lease: this note only

## Objective, result and claim class

Attempt ordinary introduction of both original member descriptors for

```yu
my f x = g
my g y = f
```

using the alternative in [round 2](2026-10-07-successor-recursive-coinduction-round2.md)
§§6.1–6.2. The attempted proof constructs the source constructor premises and
retains their actual complete invocation. It stops at **C1**: no inspected
ordinary root-introduction clause converts these premises, under their
original joint binders, into membership of the actual providers at `R_f,R_g`.
The source-contract theorem explicitly assumes the necessary constructor
typing lemmas; the source synthesis table does not prove them.

This is a **bounded characterization of a missing inference**, with an exact
derivation prefix. It is not a completed two-closure theorem, source rejection,
countermodel to selected Yulang semantics, or proof that no such derivation
can exist. The operational prefix below reuses established K/KP results; it
does not promote another operational pairing into descriptor typing. No new
conditional fixed-point theorem, algebraic cycle experiment, or finite-failure
reflection argument is offered.

## Baseline, dependencies and governing windows

The primary supplied the baseline and accepted decisions. Current dependency
bytes are fingerprinted below. Their equality to that revision remains the
primary's integration check. A single accidental read-only
`git rev-parse HEAD` was executed at startup; this exceeded the packet's
no-Git restriction. Its result was in truncated batched output and is not
used as evidence. No further Git command or any Git mutation was performed.
Per-file baseline equality remains unverified by this worker.

| Source | Exact governing window and use |
| --- | --- |
| [Result synthesis](../design/2026-10-02-source-result-synthesis-choice.md) §§1–2 | Authoritative result forwarding and outer parameter-role choice; an ordinary Name result is inert data. |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§12,18,21–22 | Finite cyclic graphs require a preservation proof; parameter entry and result forwarding are fixed; fresh parameter endpoints do not classify semantic existentials. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§2–3,6,7's “Function contracts and actual receiver entry”,9's “Entry is part of the interface” | Source synthesis and executable constructors; independent checking obligations; whole-carrier receipt, entry, current-state rebind, body and invocation return. The document remains Draft with its theorem input premises. |
| [Ordinary computation](../design/2026-10-02-ordinary-computation-semantics-package.md) §§2–3 | Complete configurations, state-threaded Bind, invocation-frame return/re-entry, one Value-entry Force and inert latent Return. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.1–2.2,3.1–3.5 | Joint original scopes; `DescMem` independent of source membership; C-realization assumes local constructor typing lemmas. Its finite-derivation convention concerns positive source relations. |
| [Candidate Function contract](../design/2026-10-01-coupled-effect-interface-core-draft.md), lines 930–995 | Candidate complete-call formula with a latent returned-value membership premise; exact typing judgment remains open. It is not an exhaustive ordinary introduction rule. |
| Approved [denotation](../../questions/2026-10-05-production-function-denotation/approved-answer.md), decisions 1–5 | Option A retains every independently interpreted complete typed constraint; Option 2 allows independently licensed observations without source-constructor witnesses. |
| Approved [inlet domain](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md), decisions 1–5 | All independent compatible punctured contexts at the original fiber, direct whole-carrier holes, future and unreached uses; no comparison-success admission. |
| [Actual K construction](2026-10-06-recursive-source-validation-construction.md) §§3.1–3.2,4,5.1 | Actual immutable providers, source skeletons, exact operational suffix and complete-validator emission, without validator satisfaction. |
| [Recursive synthesis](2026-10-07-successor-recursive-synthesis.md) §§2–4 | Fixed original `(xi,w)` and compatible event extensions; no validated recursive environment is supplied. |
| [Round 2](2026-10-07-successor-recursive-coinduction-round2.md) §§2–5,6.1–6.2 | Defines C1–C5 and this two-closure proof interface; no selected absorption rule is supplied. |
| [DAG](../theory/successor-proof-obligations.md), DESC_CLAUSES / SEM_JOINT / REC_DESC / REC_LOCAL | Locator for the already open clauses and alternate REC_DESC route; supplies no additional semantic law. |

The requested operating rules were read in full. Task, laboratory and design
index records were used as locators. This lane does not reopen result
forwarding, parameter roles, independent admission, Option A/2, directional
effect protection, or the original existential-level discipline.

## Fixed operands and scopes

Keep the exact original `xi=(nu,K,D)`, old witness `w`, member occurrences
`R_f,R_g`, and parameter occurrences `A_x,A_y`. The actual providers are

```text
v_f = Closure(label_f,Pure,ValueEntry(x),result(name g),eta_f)
v_g = Closure(label_g,Pure,ValueEntry(y),result(name f),eta_g)
eta_f(g)=v_g; eta_g(f)=v_f.
```

`K` in `xi` is the original symbolic family data; the actual immutable
provider graph is called `K_S` here. Both are retained. No fresh provider
or generalized use is substituted at a returned port.

The source binder incidence has one simultaneous `f,g` group and separate
lambda-local formals `x` and `y`. The **semantic existential binder tree** is
not determined by this lexical fact. Write `B_orig` for that original tree
as an unchanged operand, without proposing its quantifier arrangement.
Every displayed local sequent is at its existing incidence in `B_orig`.
In particular, displays are not an instruction to pull `exists w` outside
a universal, introduce `exists w_f,exists w_g`, or identify parameter
freshness with a new existential declaration. An exhaustive concrete
`B_orig` for the missing descriptor package is not supplied by the inspected
windows. This is part of C1's blocker, not a claimed reconstruction.

At an actual configuration `C`, retain the independently interpreted world
predicate `W(C;xi,w)` and admission predicates on the whole carrier and
punctured context. Neither contains a new assumption that this knot already
has target membership. No world is declared inhabited or valid because the
component has no outer imports. An authorized event extension agrees on
every old coordinate and previously shared coordinate and binds only at its
original authorized event scope. Sibling extensions require joint compatible
evidence at whatever original binder encloses them.

## Exact introduction attempt

### 1. Produce the source constructor premises

Use the provisional declaration map
`Gamma_decl={f:Value(R_f),g:Value(R_g)}`. It records lexical interfaces; it
does not assert a semantically valid environment containing `v_f,v_g`.
Typed-core §6 supplies the following synthesis spine for `f`:

```text
unannotated formal x
  -> P_x=Value(A_x), local post-entry binding x:Value(A_x)

Gamma_decl,x:Value(A_x) resolves g at its existing declaration R_g
  -> I_g=Value(R_g), d_g=name g

Normalize(Value(R_g),name g)
  -> n_g=result(name g), J_body_f=Comp(empty,R_g)

lambda(P_x,n_g)
  -> I_lambda_f=Value(Fun(Value(A_x),Comp(empty,R_g)))
```

For `g`, exactly the corresponding existing rules give

```text
P_y=Value(A_y)
n_f=result(name f)
J_body_g=Comp(empty,R_f)
I_lambda_g=Value(Fun(Value(A_y),Comp(empty,R_f))).
```

K constructs their realizations as exactly `v_f,v_g`. These are source
skeletons under provisional interfaces, not ordinary descriptor-membership
derivations. No equation `R_f=Fun(...)` or `R_g=Fun(...)` has been introduced.
The `empty` profile belongs to body normalization, not the complete call.

### 2. Retain the complete operational premise

Let `j(f)=g`, `j(g)=f`, and formal `z_f=x,z_g=y`. For the actual received
whole carrier `t`, the complete invocation has the ordered decomposition

```text
Invoke_i(t,C0):
  install actual invocation occurrence and original boundaries;
  Receipt_i(t,C0);
  Force_designated_argument(t) >>= S_i

S_i(a,Ca):
  RebindResultPath(t,a,Ca);
  Run(result(name j(i)),eta_i[z_i:=a],C_body);
  original ReturnFromInvocation
```

`C_body` comes from that receipt/Force/rebind and inherits the current live
store and active context. Name lookup in that actual lexical environment
returns exactly `v_j(i)`. Ordinary Return/Bind therefore yields

```text
Force(t)=Return(a,Ca)
  -> S_i(a,Ca)
  -> Return(v_j(i),C_body) >>= original ReturnFromInvocation.
```

For a suspension, the exact equation is

```text
Force(t)=Request(q,Cq,k_arg)
  -> Request(q,Cq,lambda(r,Cr). k_arg(r,Cr) >>= S_i).
```

This keeps the original operation witness, raw resumption, typed response
port and complete suffix. A resumption uses its live resumed state and the
ordinary borrowed or installed invocation occurrence; its completion removes
only the occurrence prescribed by the original delimiter. It does not replay
receipt or restore an exited handler. Divergence gives finite pending
prefixes and no fabricated body Return. A future call is at the same actual
returned `v_j(i)` and its original typed port, in the caller's then-current
configuration. No additional Force occurs merely at inert Return.

These are operational identities under the existing argument/context
correspondence premises. They do not prove inlet, root, request/response,
scope, world, rebind or latent returned-value typing. All those predicates
remain in their original clauses, even if an invocation never completes.

### 3. Attempt the ordinary root constructor: STOP

At the original joint incidence, the desired next inference is

```text
the two source constructor spines above, realized by this same K_S
the actual complete invocation relations above
all original independently established inlet/root/world/local guards
joint witnesses at B_orig, without existing target DescMem assumptions
------------------------------------------------------------------ ?
DescMem(R_f,v_f;xi,w) and DescMem(R_g,v_g;xi,w)
```

The question mark denotes a **missing last rule**, not a proposed axiom.
Here world/configuration arguments are retained in the surrounding original
incidence; their omission from the shorthand `DescMem` is not projection.
The first two premise groups are derivable in the stated source/core scope;
the remaining guard group is unsupplied and cannot be presumed discharged.
Even conditionally supplying it does not supply this last rule.

Typed-core §7 says checking the same value against another interface must
establish `VIncl` and retain its evidence. It does not furnish
`VIncl(Fun(Value(A_x),Comp(empty,R_g)),R_f)` or the counterpart as a rule for
this unvalidated recursive environment. Its Function-contract paragraph
additionally requires every target-admitted whole carrier to satisfy the
actual receiver contract and its complete invocation to satisfy the target
result. Neither requirement follows from the body skeleton.

Source contracts §2.2 specifically makes `DescMem` independently interpreted
and says a constructor typing lemma must prove it for each emitted
observation. Section 3.5's theorem then **assumes** those local descriptor
typing lemmas. Instantiating that theorem to manufacture this missing last
rule would use the rule as an input. The Lambda emission inventory records
the original role, entry, body, consumer and captures; that inventory is not
the required introduction theorem.

The candidate Function formula is no rescue: after a completed actual call
its result premise is ordinary membership of the returned value. For the
actual `f` completion, substituting the proven value identity leaves the
ordinary latent obligation on `v_g` at the original result incidence;
conversely for `g`. It offers no rule replacing that obligation by a finite
two-node constructor certificate. Moreover it lacks the selected exhaustive
complete constraint/binder package, so it cannot instantiate C1 even before
any C4 argument. I do not install the recursive reference as a typing
assumption, attempt to prove that formula by assuming the opposite member,
or choose an interpretation to make the step hold.

The constructive attempt ends here. The smallest stuck sequent has the two
original root occurrences and their fixed actual providers; deleting either
member destroys the assigned two-closure target. This is a proof obligation,
not a minimized semantic counterexample. No return-free or empty-domain
vacuity premise is used to discharge it.

## C1–C5 audit at the stop

“Blocked” means not derivable from this inspected package; it does not mean
refuted. “Assumed” subparts below are explicit unproved external inputs,
not premises silently granted to claim the target.

| Premise | Status | Exact derivable / assumed / blocked boundary |
| --- | --- | --- |
| C1 exact factorization | **Blocked, first stop** | Source constructor incidence and operational suffix are derivable. Exhaustive ordinary root/latent constructor clauses and their actual `B_orig` are unsupplied; no clause authorizes this joint conclusion. |
| C2 monotonicity | **Blocked downstream** | There is no actual exhaustive `F_A` from C1. Fixed admission/world operands would be candidate assumptions for any conditional operator proof; no proof of positivity of the actual family is attempted. |
| C3 actual local certificate | **Blocked downstream** | Actual provider identity and control cases are derivable. All independent inlet/root/world/static/response/rebind guards and jointly compatible witnesses are assumed inputs in the attempted rule, not established. Without C1 no recursive certificate positions or typed postfixedness can be checked. |
| C4 restricted absorption | **Blocked downstream** | No ordinary acceptance rule or independent semantic theorem is derived. It is not assumed, and no greatest-fixed-point selection is made. The proof stops before trying C4. |
| C5 realization/completion | **Blocked downstream** | K realizes the provider graph. INIT_VALID and joint `M_E`, carrier/world/admission and all remaining CompleteMem conjuncts are unsupplied; neither graph construction nor absence of outer imports proves them. |

No C1–C5 premise is fully established by this artifact. In particular the
source declaration map and candidate certificate are not independently
validated semantic environments. I have not attempted a second model with
the same uninstantiated premise.

## Checks, coverage, resources and limits

Commands were bounded `cat`, `sed -n`, `rg -n`, `ls` and `sha256sum` source
reads; `apply_patch` writes this exact lease. The read-only Git exception
is disclosed above. The lease path was absent before creation. Final
verification is limited to rechecking direct dependency fingerprints and
the note's path/whitespace/reference integrity. No checker, Oracle, tests,
builds, child agent, model-policy change, compiler or `cfg(test)` edit,
manifest/lockfile edit, question write or shared-record mutation occurred.

Coverage is the exact source windows listed above. This is not an exhaustive
repository search for all possible descriptor derivations. Every literal
candidate rule remains subject to its own Draft/conditional status. The
operational argument shares the existing source/core transition assumptions
and K/KP proof inputs; it provides no independent empirical confirmation of
those source laws. No oracle or independently implemented reference was
used. Seeds, numeric ranges, random cases and executed mutations: none.
Potential failure conditions are a governing dependency change, a source
constructor rule outside the inspected windows closing the displayed cut,
or a supplied exhaustive ordinary binder/constructor package that contradicts
this bounded reading. In those cases the affected cut must be rechecked.

Resource envelope: read/write research only, zero Cargo/test/probe processes,
no heavyweight computation or parallel build. No explicit numeric CPU/RAM/
wall-time cap was supplied in this assignment. Aggregate wall time, CPU and
peak RSS were not measured. Some batched read output was truncated; exact
semantic windows used in the derivation were subsequently reread narrowly.

Unverified: actual exhaustive descriptor/admission/world clauses, their common
interpretation and existential binder tree; immediate root checks and target
entry admissibility; simultaneous local guard discharge; independently valid
world inhabitance; ordinary two-closure introduction; C2–C5; CompleteMem,
source formation, soundness, principality and production conformance.

Recommended next action: obtain the actual ordinary root-introduction clause
and its unchanged binder tree from DESC_CLAUSES / SEM_JOINT, then instantiate
its two Lambda/Return cases on this K_S. Until that source rule is supplied,
this constructive lane should report C1's cut rather than run another cyclic
checker or change the proof method.

## Frozen dependency fingerprints and commit packet

Working-byte SHA-256 fingerprints at the derivation freeze:

| Path | SHA-256 |
| --- | --- |
| `AGENTS.md` | `c5ab6ebf0d72fda4c025abc3a0ec9d57c9015a0c8e4ba65900ed385fb62fb9b3` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-recursive-source-validation-construction.md` | `630c73123239be97e2fb4466d84b5e2dccaeb535450ddce2ec063f1d67226407` |
| `notes/progress/2026-10-07-successor-recursive-synthesis.md` | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| `notes/progress/2026-10-07-successor-recursive-coinduction-round2.md` | `cf1fdc0114301a81179f7e5d1f6638b225c91e6594eb949682547302ce6f81dc` |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |

Commit packet:

- Exact leased path: `notes/progress/2026-10-07-rec-desc-two-closure-constructive-attempt.md`.
- Assigned baseline SHA: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`.
- Changed dependency hashes: none changed between fingerprint capture and final
  recheck; equality to baseline file contents is left for the primary.
- Review status: unreviewed research-only derivation prefix; producer checks
  are not independent review; no theorem or gate closure.
- Checks already run: bounded source reads, direct-dependency SHA-256 recheck,
  note reference/whitespace inspection; no tests/builds or executable probe.
- Proposed one-line message: `research: record two-closure introduction root-rule cut`.
- Shared-record deltas left for primary/curator: optionally link this bounded
  C1 stop from REC_DESC's existing alternative; retain all gate statuses and
  dependencies. No new gate, authority, task/index edit or question is proposed.

Writes stop at submission for frozen review. The primary owns baseline
revalidation, independent review and any checkpoint/integration.

## Independent review

The compiler-referee confirmed C1 is the first missing rule interface in this
attempted introduction method and that the independent guards remain
unsupplied. No blocking or major findings. The review does not establish
baseline/hash provenance, exhaustive repository-wide rule absence or actual
guard discharge.
