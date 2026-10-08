# Flat Apply: retained source origins and the original Application owner seam

Date: 2026-10-08
Baseline: `cf345b6b4b70d29a75472cc9890077eebee31997`
Branch: `research/simple-sub-intrusion`
Status: frozen unreviewed research; non-authoritative bounded code derivation and conditional constructor schema
Exclusive lease: this file only
Method: forward evaluation of parser/HIR/source-generator constructor branches, followed by substitution into the already selected O0/O1 laws
Production implementation, new semantics, independent review and gate closure: none

## 1. Objective and exact result

Fix the supplied source:

```text
my apply f = f 1; my id x = x; pub out = apply id
```

The retained structural evidence identifies two applications, their distinct
operands and their resolved declaration/formal origins. For the inner `f 1`,
the current source generator returns a pending source-reference record, with
no argument Name use. It does not produce an original Application checking
origin or original Gen-Call-0 membership. The selected static O0/O1 constructors
therefore give a precise conditional owner package, rather than an established
original owner for this program. Even an emitted Gen-Call-0 would not supply
the additional operand/reify/result origins required by Code-Call.

The first unresolved seam in the committed
[Apply bridge](2026-10-08-apply-native-public-export-bridge.md) is preserved and
made concrete: the owning source formation for the flat inner application
must supply its actual original emission/checking origins. No CallInitial,
I0 telescope, observation/evidence action or source-presentation insertion
rule is inferred here. This is not a source rejection or impossibility result.

## 2. Authority, hypotheses and claim classes

| Governing source | Exact use |
| --- | --- |
| [Call formation](../design/2026-10-07-original-call-formation-definition.md) §§2–4,6 | OSig-Demand and OC-CallEff operate on actual emitted records with their entire original dependent indices. No all-source generator follows. |
| [Call ownership](../design/2026-10-07-original-call-owner-definition.md) §§2–4.1,5 | Registration, resolved route and O0 introduce SharedInvoke membership; an independent SeedExposure additionally introduces paired lexical/checking facets. |
| [Source construction](../progress/2026-10-06-source-call-generation-construction.md) §§3–4.4,5,7 | Reviewed nested Name/Name singleton construction and its initial role/policy; decorated operand obligations and remaining original profile/admission cuts. |
| [Function-view direction](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5; integrated `function-call-view-formation/q1 a2` decisions 2–6 | Shared formal/use inference, provisional protection and ordinary-value refinement, preserved actual callable roles and joint `nu,K,D`. Detailed formation remains required. |
| [Nested-source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md) §§1–4; integrated nested realization `q1 a1` decisions 1–4 | Exact nested closure interpretation and its limited scope. It supplies no flat literal-argument generator rule. |
| [Call-input construction](2026-10-07-call-input-construction-proof.md) §§3.1–3.4 | Exact Code-Call/Check package and finite code construction under actual independent formation origins. |
| [Apply bridge](2026-10-08-apply-native-public-export-bridge.md) §§3–5 | Native public id is an existing operand supplier; original Application origins and complete Call introductions remain required. |
| Integrated [ReadInvoke owner answer](../../questions/2026-10-08-readinvoke-source-presentation/approved-answer.md), proposed decision items 1–4 and receipt Remaining gates | Source construction retains insertion/lookup evidence within its selected finite identity Name/Name seam. It supplies no new rule meaning, CallInitial or complete input/action law; no automatic extension to literal Apply is assumed. |

**H_struct:** the exact bytes are parsed through the repository's ordinary
empty-environment parser, with valid retained CST positions; for the module
inventory use the explicit default-off shadow application lowerer. Claims in
§3 are direct branch derivations at the pinned code, not fresh runtime results.
No satisfying typing, world, effect assignment or query is in H_struct.

**H_emit, H_reg, H_seed and H_app:** independently supplied original
derivations defined in §4. These remain missing; the schema does not assume
their conclusions or assert that the repository currently constructs them.
The resulting O0/O1 and Code-Call implications are conditional.

**Candidate assumptions excluded:** `A_f=F_c=u_Int`, empty effects, a generic
Value-implies-non-Handler rule, fresh providers per port, or interpreting
candidate solver success as original emitted membership. The bridge's
candidate identity completion remains a candidate, with all its premises.
The previously reviewed O0/O1 laws are established suppliers in their own
scope; this producer does not independently certify them or extend that scope.

## 3. Forward structural derivation

### 3.1 Parser and lexical constructor output

`expression/operator_chain.rs` `is_ml_argument`/`ml_argument` (lines 758–820)
accept the whitespace-separated same-line operand and wrap it in MlArgument;
the child is parsed with `MlMode::None`. Thus each indicated body has one
operator-chain argument, not a nested id invocation:

```text
apply body: IdentifierExpression(f), MlArgument(IntegerLiteral(1))
id body:    IdentifierExpression(x)
out body:   IdentifierExpression(apply), MlArgument(IdentifierExpression(id))
```

The ordinary association dispatcher (`yu-hir/src/lib.rs:311`) retains an
MlArgument as structural continuation. The declaration shadow projector
(`yu-hir/src/shadow.rs:2595–2742`) projects literal and Name leaves separately
and folds the tail into `Form::Apply`. Its Name map consists of actual
registered binders, so the inner f resolves to the apply formal. The
single-parameter direct-body constructor (`:1677–1721`) wraps that body in
a root Lambda with no capture:

```text
L_apply = Lambda(binding d_apply, parameter d_f,
                 body c=Apply(Use(u_f,d_f), Literal("1")), captures=[])
L_id    = Lambda(binding d_id, parameter d_x,
                 body Use(u_x,d_x), captures=[])
```

These symbols are locator names for retained branded objects. Numerical IDs,
source ranges and identical spellings are not original semantic identities.
The Lambda's typed capture/provider/receiver correspondence remains pending.
There is no local Bind, step Lambda or returned step occurrence in this source.

The ordinary module atom lowerer (`module.rs:1980–2026`) first resolves a Name
through the lexical parameter scope, then a unique module definition. Thus
f/x have their respective formal origins, and the outer apply/id Names select
their actual module definitions. Integer spelling `"1"` is retained; this
does not itself establish a hereditary ground-value/carrier contract.

### 3.2 Both retained applications and the source-generator split

Under the explicit shadow lowerer, `module.rs:1815` attaches
`UnsupportedExpression` before constructing `ResolvedExpr::Apply` at `:1930`.
`shadow_resolved_call_inventory` (`shadow.rs:156–234`) borrows these application
and operand identities with their existing errors. Its result is structural:

| Owning definition | Callee | Whole argument | Retained inventory |
| --- | --- | --- | --- |
| apply | own formal Name f | Integer spelling 1 | one Apply c |
| id | own formal Name x | none | no Apply |
| out | resolved module Name apply | resolved module Name id | one Apply o |

This is neither clean production HIR acceptance nor original Call typing.
The inventory checks source identity and error references, not semantic
membership. The declaration Skeleton projector requires a parameter
(`shadow.rs:1587`); the parameterless out declaration is outside that
projection. Its module-HIR inventory remains available. Do not pretend that
`generate_source_calls` generates out's record from a declaration Skeleton.

For the apply declaration, `SourceCallUseInput` preserves the actual direct
Use callee and the whole literal argument (`shadow.rs:1170–1257,2175–2226`).
`yu-core::shadow_call_formation::generate_source_calls` (`:118–143`) therefore
projects the following **PendingSourceCallStub** under H_struct:

```text
call=c; callee_use=u_f; argument=literal_1; argument_use=None
```

It retains all four SOURCE_BASE_UNRESOLVED entries, verbatim:

```text
CompleteEmittedOriginalCallClauseAndJointWitness
InitialSourceDescriptorRelation
FiniteSourceBaseEmissionConformanceCertificate
CompleteInvocationInterpretation
```

The original B/X/xi/type/scope, emitted membership and legal whole-action
fields are not supplied by this stub. Its empty argument-use option must not
be repaired by inventing a formal `d_1`/Name occurrence for a literal.

### 3.3 Minimized discriminating witness for the generator boundary

The standalone `my apply f = f 1` already separates pending reference
generation from the selected captured-symbolic generator. Removing id and
out leaves the same earliest missing input. This is a minimized witness for
that code-domain distinction, not a semantic counterexample or a proof of
globally shortest source text.

`generate_captured_declaration` reaches `generate_captured_from_skeleton`
(`shadow_call_formation.rs:299–361`), which requires `captured_call_input`.
That locator (`shadow.rs:2229` onward) requires root Lambda → local Bind →
local Lambda → direct Name/Name Call → returned local binding Use. For this
flat source, the root Lambda body is Apply, so the Bind match fails first.
Even replacing that topology test would leave its later argument-Use match
inapplicable to literal 1. No `SymbolicGenCall0` is constructed by this route.
The nested approved construction is retained exactly as selected.

The existing `shadow_call_formation` fixture explicitly checks the pending
stub for flat f 1; the candidate Apply fixture (`shadow_apply_candidate.rs:426`)
asserts two candidate calls and candidate Int together with unresolved
premises. These are inspected test contracts; neither target was executed
for this note. Candidate `UNRESOLVED` additionally retains application typing,
original Gen-Call-0 membership, role/protection, complete invocation, whole
argument compatibility, admission, fresh-use and scope correspondence.
The displayed Int is therefore no original owner oracle.

## 4. Exact conditional original package

Keep one actual original `(B,X,xi,Delta_c)` with `xi=(nu,K,D)`. Structural
locator c/u_f/d_f alone does not instantiate these coordinates.

**H_emit:** an actual well-scoped emitted Gen-Call-0 derivation at c supplies
the entire adopted formation tuple:

```text
e_c : Gen-Call-0 at (B,X,xi,Delta_c)
Idx(e_c)=(B,X,xi,Delta_c;
          d_f,A_f,R_f,u_f,u_arg,c,u_c,U_c,beta_c,p0_c,p_out(c),ElimOrigin_c)
U_c=F_c; beta_c=(d_f,R_f); rho_c=demand(e_c)
```

Here `u_arg` denotes the original argument occurrence required by the original
record, if its actual literal-argument rule supplies one. It is **not** a
fabricated argument Name Use. The known nested Name/Name constructor's
`u_x -> d_x` evidence cannot fill it. Its exact sort and producing derivation
must be retained from that original rule. H_emit currently has no supplier
for this flat literal case in the inspected generator.

**H_reg:** actual Reg(beta_c), including endpoint, root, original scope and
annotation provenance, and an actual Route(e_c) selecting the same d_f.
The lexical resolver supplies the source locator route; identifying that
route and registration with these original typed objects remains explicit.

Under H_emit/H_reg the selected rules compute, at these same indices:

```text
q_c = OSig-Demand(rho_c) = Inv(Id(U_c),U_c)
ce_c,kappa_c = OC-CallEff(e_c,q_c)
s_c = SharedInvoke(beta_c)
slot_c = OSlot-SharedInvoke(e_c,Reg(beta_c),Route(e_c),ce_c,kappa_c)
```

This constructs one shared immediate slot member, not the complete Slots
inventory. It establishes no semantic provider/SharedContract membership.

**H_seed:** an actual directional SeedExposure(k_c,e_c) at u_c, with the
original variable endpoint, upper demand, both occurrences and complete
source derivation. The direction is fixed; no later id-Pure fact or absence
of annotation manufactures this certificate. The reviewed S1 nested
unannotated supplier is not a derivation for this different literal case.
Under H_seed, the existing O1 constructors then give:

```text
attach_c=UpperInvokeAttachment(Reg,Route,e_c,ce_c,kappa_c,seed_c)
o_c=OwnUpper(attach_c)
lex_c : Own_orig(beta_c,s_c,u_f,p0_c,o_c;X)
chk_c : Own_orig(beta_c,s_c,u_c,p0_c,o_c;X)
```

The occurrence indices remain distinct. Legal maps must act on the entire
tuple and both facets together; their source/type/scope legality is an
independent retained premise, not supplied by the branded Rust IDs.

**H_app:** the actual original Application emission additionally supplies
the Code-Call premises from call-input §3.4: original child Code derivations
qf/qa, the literal primitive/Result law, argument ReifyOrigin and Carrier-Delay,
original VIncl and WholeArgCompatible **origins**, original complete result
and result port, and the actual-provider-dependent ordered suffix schema.
Bundling those premises yields exactly:

```text
Check_c=(e_c,qf,qa,t_arg,F_c,R_f,
         VIncl-origin(A_f,F_c),
         WholeArgCompatible-origin(J_1,CarrierContract(F_c)),
         Comp(E_c,A_c),o_result_c,Suffix_c(U_actual),
         original resolved roots/scopes and all operand incidences)
```

Formation origins are not checking truth. `U_actual` is the retained actual
provider parameter; it cannot be copied from the checked descriptor F_c.
`o_result_c` is a result port and differs from owner evidence o_c above.
Under these original premises, Code-Call forms the finite source code
certificate by its existing constructor. No CallInitial/observation membership
conclusion follows from that certificate. For outer o the analogous complete
Application package is also unsupplied; its module callee gains no formal seed
merely from an unannotated use. One cannot transfer the inner owner to o.

## 5. Evidence, omissions and stopping condition

This lane performs one forward source/artifact derivation. It does not repeat
the bridge's import replacement proof or an initial-observation probe. Once
the selected generator branch fails and leaves H_emit/H_app unresolved,
another checker implementing the same assumed Application/transition rules
would only check consistency of those assumptions. There is no independently
executed Oracle and no independent source-semantics oracle in this result.
Parser, HIR, source stubs and candidate fixtures share repository construction
assumptions; their agreement is structural evidence only.

Coverage is the exact source and its standalone inner declaration, plus the
already selected nested topology used to locate the generator's domain.
No seeds, numeric search ranges, mutation executions, performance samples,
builds or tests were run. Grouped/computed callees, annotated forms, additional
uses, arbitrary local bindings, recursion/State, whole literal-carrier
licensing, complete original profile/admission, principal export, transformed
apply/out, production Option 2 and F5 correspondence remain unverified.

Failure conditions include dependency changes; using a pending stub as emitted
membership; inserting a literal Name binder; importing nested S1 by renaming;
turning annotation absence into a generic seed rule; identifying u_f/u_c;
forgetting original joint indices; inferring checking origins from candidate
Int; or manufacturing original CallInitial/action/insertion data.

Resource budget: one documentary note, lightweight sequential shell reads and
hashing, zero heavy processes. No numeric CPU/RAM/wall-time ceiling was
supplied. Peak CPU/RAM and reasoning wall time were not instrumented. Several
initial broad reads exceeded tool-output limits; relevant governing documents
and constructor sections were subsequently read in bounded slices. Searches
were scoped to cited owners, not an exhaustive absence audit. A few guessed
HIR filenames were absent; the actual owner is `src/module.rs`.

Recommended next action: supply the actual original flat literal-argument
Application formation at c, retaining its shared formal registration, literal
whole-carrier origins and original emitted checking derivations at that owner.
Apply the already selected O0/O1 constructors only when their exact premises
are available. The later CallInitial/I0/action/insertion gate stays separate.

## 6. Frozen input hashes and commit packet

The following direct semantic/source dependencies match their pinned baseline
bytes; the final producer report records the frozen output hash and recheck.
All approved-answer/receipt files used above also match that committed revision.

```text
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110 notes/design/2026-10-07-original-call-owner-definition.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0 notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
9f645f961cc88a5089973476989465173f57fa6d5787b609ccd879f47c3530c0 notes/theory/2026-10-08-apply-native-public-export-bridge.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d crates/yu-syntax/src/expression/operator_chain.rs
c3e092fa2ac0dca320b9e0327a87363ccc0e9c10c07512f52328172df2be6d2b crates/yu-hir/src/lib.rs
3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363 crates/yu-hir/src/module.rs
5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f crates/yu-hir/src/shadow.rs
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb crates/yu-core/src/shadow_call_formation.rs
1897d6bbd4e9b7e6ef6b839abdfc1943bd515c2c7cab8cb71277e8aa2925b0e2 crates/yu-core/tests/shadow_call_formation.rs
2b59eb0b327df89a5fbfb5373de9f01f73c0aaeca06b406c289e4aa7f5116dc3 crates/yu-solver/src/shadow_apply.rs
93506b15b5b0371570255a89642dca04d6fc7c54f0a78b4ab9ba4e77d5499b0c crates/yu-solver/tests/shadow_apply_candidate.rs
```

- Exact leased path: `notes/theory/2026-10-08-apply-original-application-owner-derivation.md` only.
- Baseline SHA: `cf345b6b4b70d29a75472cc9890077eebee31997`.
- Changed dependency hashes: none.
- Claim/review status: bounded structural derivation and conditional original package; frozen unreviewed research; no independent review claimed.
- Checks already run: scoped `rg`/`sed`/`cat` constructor audit, `git show <baseline>:<path>` byte comparison and SHA-256 capture; final note/link/whitespace and dependency checks are reported with submission. No compiler commands.
- Commit-ready: eligible only for an honest research-only checkpoint after the primary inspects the frozen exact lease and confirms unchanged dependencies/no accepted blocking finding. This does not close a gate.
- Proposed checkpoint message: `research: derive flat Apply origins and isolate original Application owner inputs`.
- Shared-record deltas intentionally left for primary/curator: record the structural pending stub and conditional H_emit/H_reg/H_seed/H_app package; preserve the inner Application, literal carrier, CallInitial/I0/action/insertion, outer Apply and production gates. No task/index/authority/theory-map/question-board write or status promotion is proposed.

Writes stop before submission for frozen review.
