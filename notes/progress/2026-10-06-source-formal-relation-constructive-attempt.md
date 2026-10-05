# Constructing the exact candidate's open source/formal relation

Date: 2026-10-06
Baseline: `cf4ffa4484d701ab85b4f5f9be429a71fe482c33`
Status: frozen, unreviewed research checkpoint; conditional construction and reduced unproved leaf
Lease: this note only
Objective/method: compositional proof construction for `my apply f = { my step x = f x; step }`; evaluate a symbolic relation through Name, Call, Lambda, Bind and Result rather than invert a completed registration consequence.
Implementation authority: none

## 1. Authority and precise claim classes

The Authoritative inferred-call-views §§2–5 and nested-block addendum §§1–4,
including the integrated call-view q1/a2 and nested-block q1/a1 answers and
receipts, fix the source meaning and required direction. Typed-core §6 is a
reviewed **conditional Draft construction**, not another source decision.
Source-contract §§2–3 is a **reviewed conditional package**, whose independent
primitive interpretation and decorated-input hypotheses must be retained.
The reviewed Q-independent generation candidate names the still-missing
constructors; its judgment interface is not an admissible rule.

Established decisions: sequential local binding; final `step` returns the
function; inner `f` resolves to the outer formal; inner `x` resolves to its
own formal; the returned closure retains that outer `f`. One shared inferred
relation and original joint `(nu,K,D)` are required; Q supplies no formation
evidence. Annotation absence requires fully protected provisional Handler
treatment, followed by the selected ordinary-value determination on the same
inferred formal/use relation. Actual supplied callable role and entry remain
those of that callable.

Conditional result below: relative to the admitted ordinary §6 skeleton,
one independently interpreted, source-scoped whole-tuple call relation, and
its local typing/capture certificates, the exact candidate composes to a
single shared open relation. Its block returns the closure template without
executing the latent call. Composition adds no choice of a satisfying fiber,
no independent port witness, and no Q input. This is **not** source generation
of those premises. The constructive attempt stops at the first missing
semantic constructor; it does not establish impossibility, principality,
source adequacy, current production acceptance or admission/conformance.

## 2. Smallest ordinary constructor prefix

Write `b_f,b_x,b_s` for the outer formal, inner formal and local binding;
`u_f,u_x,u_s` for the corresponding name occurrences; `c=Apply(u_f,u_x)`.
Let `L_s` denote the local lambda. The approved resolver facts are

```text
resolve(u_f)=b_f; resolve(u_x)=b_x; resolve(u_s)=b_s
CaptureUseIncidence(L_s,b_f,u_f,position(u_f)).
```

The candidate has no recursive reference. No local generalization policy is
chosen. Under §6's admitted ordinary parameter/name/binding constructors,
introduce symbolic endpoints `A_f,A_x,E_c,A_c,E_b` once at their original
scopes and use the environments

```text
Gamma_f  = Gamma_0[b_f:Value(A_f)]
Gamma_fx = Gamma_f[b_x:Value(A_x)].
```

Endpoint introduction here is the §6 skeleton construction, not allocation of
a complete boundary or profile. Resolved Name copies the existing environment
entry. The actual outer callable's value entry owns rebind of `b_f`; lookup
inside `step` does not perform that entry again.

The following are constructed interfaces and obligations, not solved typing
certificates:

```text
u_f : Value(A_f)         n_f = result(name b_f)
u_x : Value(A_x)         n_x = result(name b_x)
c   : Computation(E_c,A_c)
                         n_c = Normalize(I_c,reify(call(n_f,n_x)))
A_s = Fun(Value(A_x),Comp(E_c,A_c))
L_s : Value(A_s)         n_s = result(lambda(Value(A_x),n_c))
u_s : Value(A_s)         n_u = result(name b_s)
block : Computation(E_b,A_s)
                         n_b = Normalize(I_b,reify(bind(b_s,n_s,n_u)))
apply : Value(Fun(Value(A_f),Comp(E_b,A_s))).
```

The administrative Normalize/eliminate/reify pairs can be retained. Their
same-context contraction is conditional on the admitted core law and moves
across no boundary. `E_b` is constrained by the existing complete Bind image;
no effect-row union or solved empty-effect inference is used. `Fun` here is
the closure body/result skeleton. It does not equal a complete invocation
descriptor: §9 retains argument entry and the designated consumer in `J_call`.

The application row generates the following **obligation record**:

```text
O_c = (callee-root=b_f via u_f,
       whole-argument=Comp(empty,A_x) via u_x,
       complete-invocation-endpoints=(E_c,A_c), source-occurrence=c).
```

§6 warrants the callee Function constraint and whole-argument/typed-boundary
obligation. It does not specify an exhaustive semantic predicate for this
unknown callee, nor the provisional-role discharge rule. In particular,
`Value(A_x)` generates value evidence at `u_x`; it is not a theorem that every
actual callable consuming its carrier has Pure role or value entry.

## 3. An explicit symbolic relation and its compositional evaluation

This section constructs a relative relation, with its unproved leaves visible.
Let `xi=(nu,K,D)` retain the original source scopes. Let `z` collect the
original shared tuple (environments, source/capture incidences and proof
witnesses); it is not a new source existential type. Introduce two leaves:

* `Omega_S(xi,z)`: the independently source-derived admissible fiber envelope,
  including scope and active original dependencies. This is **unproved** for
  the undecorated candidate. Taking every arbitrary K,D as an admissible fiber
  would not derive it.
* `T_c(xi,z;A_f,A_x,E_c,A_c,r,e)`: the independently interpreted whole-tuple
  callable/argument obligation at `O_c`, including local descriptor typing,
  original incidence and complete-call interpretation. This is **unproved**
  as a source constructor. `r,e` describe the actual provider when instantiated;
  they are not assigned by the inference seed. The future profile/receipt
  clauses must be present at their proper static/event stages, not fabricated
  from these two symbols.

The explicit candidate relation is the following open expression:

```text
R_c = { (xi,z,A_f,A_x,E_c,A_c,r,e) |
          Omega_S(xi,z) and T_c(xi,z;A_f,A_x,E_c,A_c,r,e) }.
```

All admissible fibers are retained by this comprehension; there is no
`choose xi`, per-port solution, or restriction to a terminating observation.
This does not prove that Omega_S is complete or that T_c has an independent
interpretation. Their source derivation is exactly the missing premise.

For a row of this relation, keep the **same** xi,z and original environment
`eta`. Denote `eta[b_f]` by `f`, and an inner rebound value by `x`. The
Name/Result constructor expressions are

```text
N_f(xi,z,eta,C) = Return(eta[b_f],C)
N_x(xi,z,eta[b_x:=x],C) = Return(x,C)

J_c(xi,z,eta[b_x:=x],C)
  = ExecuteCallable_c(eta[b_f], Delay(Return(x)), eta[b_x:=x], C).
```

The last line is the conditional Call constructor image: the callee is
looked up once from the original shared root and the **whole** argument is
inert. It includes the actual callable's entry, receiver/receipt, body,
designated consumer and return, as source-contract §3.2 requires and typed-core
§9 distinguishes from `J_body`. It is a relation, so Return/Request/divergent
prefix cases are not replaced by a chosen successful result. A type-shape
test, known Pure input, or Q result is absent. We have not derived its missing
typed-boundary inputs by spelling ExecuteCallable.

Now apply the closure constructor symbolically:

```text
s_eta = ClosureTemplate(L_s, Value(A_x), J_c,
                        lexical-capture=(b_f,eta[b_f]))
R_step(xi,z,eta,C) = Return(s_eta,C).
```

`ClosureTemplate` is proof notation for the existing lambda constructor and
captured-root references, not an added representation/carrier or an allocation
proposal. Its template retains the whole row of R_c and the same xi,z. It
does not execute J_c. Lexical capture of `eta[b_f]` is approved; attachment of
typed evidence remains the separate unproved A obligation.

Bind/Name/Result can now be evaluated explicitly using §3.2's Return law:

```text
R_block(xi,z,eta,C)
  = Return(s_eta,C) >>= ((s,C') -> Return(s,C'))
  = Return(s_eta,C).

R_apply = ClosureTemplate(L_apply,Value(A_f),R_block,capture=Gamma_0).
```

The conditional equality is pointwise at every retained row of R_c. No
existential elimination occurs on xi,z, so the returned template contains the
same latent callee root and full correlated fiber. Outer value entry later
receives/forces/rebinds its actual argument before R_block, while inner entry
receives/forces/rebinds its own argument before J_c; closure construction
executes neither. This evaluation establishes composition and the return
prefix, not the validity of T_c, event receipt, or typed capture transport.

For bookkeeping one can take the role-indexed relational root

```text
F_open(b_f;u_f,c) = R_c with the callee-root reference fixed to b_f.
```

This supplies an explicit **candidate presentation** of the requested shared
relationship, retaining every role/entry coordinate admitted by the leaves.
It does not warrant `|-gen F_cb`: calling R_c a Function relation would
otherwise hide its missing T_c/Omega_S interpretation and role/protection
laws. The existing conditional relation constructors prove composition only
after their independently typed primitive leaves are supplied.

## 4. Where the source judgment cannot be formed

The first absent rule is a constructor from the exact resolved component plus
O_c to a source-interpreted role-indexed primitive, together with its scoped
fiber envelope. Its needed type is approximately

```text
S_exact; resolve(u_f)=b_f; O_c; OrdinaryValueUse(u_x)
  |-formal  (F_open, Omega_S, T_c, source-correspondence).
```

This is a required interface, **not an adopted rule**. Its conclusion cannot
simply be premises `CompleteFormal(F_cb)` or `TypedCall(T_c)`. §6 gives O_c
and the value tag; source-contract §2.1 admits an independently interpreted
Primitive and Constructor image; neither clause supplies the interpretation
that the new rule would need. §2.2 requires active predicates rather than
explaining metadata. §3.1 supplies decorated roles/paths/owners/receipts and
the original tuple; it is not an inference from the resolver facts. §3.2
preserves those fields in each source image. §3.5 additionally assumes local
descriptor typing and finite conformance.

| Required field | Available construction / exact unresolved premise |
| --- | --- |
| Shared `b_f,u_f,c` reference | Approved lexical map plus §6 Name reuse and Call obligation; no solved callee shape needed |
| Ordinary `x` evidence | §6 unannotated parameter, Name and Result; discharges only the source Value tag |
| Open actual role/entry coordinate | Retained in the hypothetical independently interpreted whole Call tuple; no rule assigning or rewriting it |
| Provisional Handler seed and later non-Handler determination | Call-view §3 selects both stages, but supplies no operator relating the two on T_c; cannot encode the seed as actual `r=Handler` |
| Full protection from annotation absence | Call-view §4 fixes the requirement; contribution/profile generation and protection predicate remain unproved; an empty row is not a substitute |
| Static beta and complete Slots(beta) | Call-view §2 requires position **and completed contract**; the source label c or b_f is only the position/reference, not this constructor |
| Original nu,K,D and admissible fibers | Retained unchanged by §2.1 conjunction and supplied scoped constructor images; derivation of Omega_S and all original incidences remains unproved |
| Typed paths, Flow, owner/receiver correspondence | §3.1 supplied decoration and §3.2 retained incidence; lexical capture/endpoint sharing alone supplies no typed proof |
| Event receipt | Separate `|-recv` from the reviewed candidate, after an admitted instance and actual entry; no receipt during static lambda formation |
| A capture attachment / lookup | Separate later judgments; lexical root retained here, typed packet attachment/lookup remains unproved |
| Complete admission | §3.3's independent history/context inventory is a premise; no use of Q or Return-prefix existence can initialize it |

Thus the attempt reaches a useful compositional identity while stopping short
of generating a complete formal relation. Selecting a concrete semantics for
T_c, its role-stage operator or source K,D would cross the stated approval
boundary. No such selection is made. This is one new constructive attempt;
further consequence inversion or a larger toy checker would leave that same
primitive premise untouched.

## 5. Evidence limits, mutations and resources

No checker, source test, build, Oracle query, legacy search or Git mutation was
run. The reference is the approved source meaning plus the expressly
conditional relational clauses. Source-contract §2.1 and §3.2 are shared
assumptions of both the expression and its evaluation: the Return/Bind identity
is therefore a conditional derivation, not independent source validation.
There is no exhaustive search, random seed, finite provider range or minimized
accepted-source counterexample in this lane.

Named proof mutations and their failure conditions:

1. Replace `eta[b_f]` at u_f with a fresh unrelated provider root: violates Name
   reuse/approved capture before any Call interpretation is consulted.
2. Give each operand its own xi and combine successful projections: the
   displayed relation and constructors no longer evaluate on one original
   tuple; invalidates the shared-fiber argument.
3. Evaluate J_c while constructing s_eta: violates inert Lambda/Result and
   changes the returned-function prefix.
4. Encode the provisional seed as actual `r=Handler`, then rewrite r from
   Value(A_x): violates the actual-role boundary; no derived refinement rule.
5. Let Q success define T_c, Omega_S or beta: destroys source/admission
   independence. Syntactically omitting Q elsewhere does not repair it.

These are analytical mutations; no executable mutation campaign is claimed.
Even an interpreter agreeing with this expression would share the supplied
primitive assumptions and would not prove them.

The single exact source graph is the coverage envelope. Omitted: repeated or
mixed callee uses, recursion, annotation-present removal, generalization and
fresh-use preservation, implicit adapters, handler images, production Option
A/Option 2 extras, arbitrary future challenge formation and source adequacy.
No finite support or termination restriction was imposed on the symbolic
relation; absence of such a restriction is not proof of exhaustive admission.

Resource budget: at most 12 sequential lightweight source/read/search commands
after mandatory policies, one note, no compiler processes, 20 minutes maximum.
At preparation of this note, eight such source/read commands were consumed;
one final dependency/scope inspection is planned (nine total). All recorded
commands were subsecond; exact agent wall time/peak RSS were not instrumented.
No additional search range or unfinished enumeration exists. The initial
locator rg output and one combined source read were truncated; the decisive
source-contract §§2–3.5 text was subsequently reread narrowly and all governing
call-view/addendum/candidate content was obtained. No broader search is claimed.

Recommended next action: construct an independently grounded interpretation
of the single role-indexed formal Call primitive at O_c, including source
fiber scope and the approved seed/refinement operator; test its proposed
clauses against a distinct source pattern before adopting it. Beta/profile
completion and later event/A evidence remain subsequent obligations.

## 6. Frozen dependencies and commit packet

The live dependencies matched the pinned baseline in the pre-write path-scoped
diff; integration receipts identify accepted commits `61a3651376166346a5baa03ec6679c310b0edbdb`
and `a6bdcf99fba35497cf1323c70101e34669a3ba71`. Direct dependency SHA-256 values:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-qind-source-generation-judgment-candidate.md` | `27aa739681078a4ec574d1075869469a281af468ab9a32f3166be3c79df07d78` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

Commit packet:

* Exact leased/changed path: `notes/progress/2026-10-06-source-formal-relation-constructive-attempt.md` only.
* Baseline SHA: `cf4ffa4484d701ab85b4f5f9be429a71fe482c33`.
* Changed dependency hashes: none observed; revalidate the table before integration.
* Claim/review status: frozen unreviewed conditional research construction; author self-inspection is not independent review. No gate promotion or authority.
* Checks: narrow source reads; baseline-scoped dependency diff; SHA-256 capture; original-scope symbolic substitution and Return/Bind calculation by derivation. No tests/builds/Oracle/Git mutations.
* Proposed commit message: `research: compose exact candidate open formal relation conditionally`.
* Shared-record deltas left for primary/curator: optional locator in `tasks/current.md`; record that ordinary Name/Call/Lambda/Bind composition preserves a supplied single joint relation, while independently interpreted source formal Call, admissible fiber generation, role seed/refinement, static profile and typed receipt/A transport remain open. No shared-file edits or design-status promotion proposed.
